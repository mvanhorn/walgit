-------------------------- MODULE WALCheckpoint --------------------------
(***************************************************************************)
(* Manifest-CAS commit protocol for walgit, focused on the checkpoint /    *)
(* log-trim interaction (audit finding C2).                                *)
(*                                                                          *)
(* The bucket's `manifest.pb` is the single linearization point.  A        *)
(* checkpoint folds the log up to some seq S: it sets checkpoint.seq = S,   *)
(* min_seq = S+1, and drops every log segment whose last_seq <= S.  The     *)
(* commit is a compare-and-swap on the manifest version token (`revision`). *)
(*                                                                          *)
(* Abstraction: segments always cover [segLo, head] contiguously (they are  *)
(* appended contiguously in practice), so the whole live segment set is the *)
(* single number `segLo`.  `rev` is both the monotone revision and the CAS  *)
(* token: `myVer[i] = rev` means "no manifest write since instance i read". *)
(*                                                                          *)
(* Fix (a CONSTANT): FALSE models the historical bug, which only returns    *)
(* when cpSeq >= head. TRUE models the fixed guard: also return when the   *)
(* fresh checkpoint has reached the sequence this writer already            *)
(* materialized.                                                            *)
(* The intended sequence is never recomputed: its immutable candidate is    *)
(* already bound to that sequence and attempt.                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Instances, MaxSeq, Fix

VARIABLES
    head,     \* manifest head_seq
    cpSeq,    \* manifest checkpoint.seq (0 = no checkpoint yet)
    minSeq,   \* manifest min_seq
    segLo,    \* lowest seq still covered by a live log segment
    rev,      \* manifest revision == CAS version token (monotone)
    phase,    \* [Instances -> {"idle","wrote"}]
    myVer,    \* [Instances -> Nat] manifest version each instance last read
    mySeq     \* [Instances -> Nat] fold seq each instance intends to commit

vars == <<head, cpSeq, minSeq, segLo, rev, phase, myVer, mySeq>>

Init ==
    /\ head   = 1
    /\ cpSeq  = 0
    /\ minSeq = 1
    /\ segLo  = 1
    /\ rev    = 1
    /\ phase  = [i \in Instances |-> "idle"]
    /\ myVer  = [i \in Instances |-> 0]
    /\ mySeq  = [i \in Instances |-> 0]

(* A background push (or compact) appends one entry and bumps head + rev.    *)
(* Segments still start at segLo, so segLo is unchanged.                     *)
Push ==
    /\ head < MaxSeq
    /\ head' = head + 1
    /\ rev'  = rev + 1
    /\ UNCHANGED <<cpSeq, minSeq, segLo, phase, myVer, mySeq>>

(* Round 1 of a checkpoint on instance i: read the manifest, write the       *)
(* immutable checkpoint + refs objects (no manifest mutation yet), and       *)
(* remember (version read, seq to fold to = current head).                   *)
CkStart(i) ==
    /\ phase[i] = "idle"
    /\ head > cpSeq
    /\ phase' = [phase EXCEPT ![i] = "wrote"]
    /\ myVer' = [myVer EXCEPT ![i] = rev]
    /\ mySeq' = [mySeq EXCEPT ![i] = head]
    /\ UNCHANGED <<head, cpSeq, minSeq, segLo, rev>>

(* Round 2 idempotency/anti-regression guard. The second disjunct is the fix:*)
(*   if cpSeq >= mySeq[i] || cpSeq >= head { return }                        *)
CkCommitIdem(i) ==
    /\ phase[i] = "wrote"
    /\ \/ cpSeq >= head
       \/ /\ Fix
          /\ cpSeq >= mySeq[i]
    /\ phase' = [phase EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<head, cpSeq, minSeq, segLo, rev, myVer, mySeq>>

(* Round 2, CAS succeeds (our read is still current).  Commit the fold at     *)
(* mySeq[i] -- STALE under the bug.  Trim: segments with last_seq <= s are    *)
(* dropped, so segLo rises to s+1 only when s+1 exceeds the current segLo.    *)
CkCommitOk(i) ==
    /\ phase[i] = "wrote"
    /\ cpSeq < head
    /\ (~Fix \/ cpSeq < mySeq[i])
    /\ myVer[i] = rev
    /\ LET s == mySeq[i] IN
         /\ cpSeq'  = s
         /\ minSeq' = s + 1
         /\ segLo'  = IF s + 1 > segLo THEN s + 1 ELSE segLo
         /\ rev'    = rev + 1
    /\ phase' = [phase EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<head, myVer, mySeq>>

(* Round 2, CAS fails (412): someone wrote since our read. Re-read the        *)
(* version and retry without changing mySeq; the anti-regression guard is    *)
(* re-evaluated against the fresh cpSeq before either retry action can fire. *)
CkCommitRetry(i) ==
    /\ phase[i] = "wrote"
    /\ cpSeq < head
    /\ (~Fix \/ cpSeq < mySeq[i])
    /\ myVer[i] # rev
    /\ myVer' = [myVer EXCEPT ![i] = rev]
    /\ UNCHANGED <<head, cpSeq, minSeq, segLo, rev, phase, mySeq>>

WorkNext ==
    \/ Push
    \/ \E i \in Instances :
         CkStart(i) \/ CkCommitIdem(i) \/ CkCommitOk(i) \/ CkCommitRetry(i)

Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                              *)
(***************************************************************************)

(* Contiguous reference only. Public segments may contain burned gaps and
   genesis is special: use proto invariants, not this equality, in Rust. *)
SegAtMin == segLo = minSeq

(* Proto: min_seq == checkpoint.seq + 1 when a checkpoint exists.           *)
MinIsCp == (cpSeq = 0) \/ (minSeq = cpSeq + 1)

(* Durability / read-your-writes: every committed seq in 1..head is         *)
(* reconstructable = folded into the checkpoint (<= cpSeq) OR still in a     *)
(* live segment (>= segLo).  A gap here is silent data loss on cold start.  *)
NoGap == segLo <= cpSeq + 1

CpBounded == cpSeq <= head

TypeOK ==
    /\ head   \in 0..MaxSeq
    /\ cpSeq  \in 0..MaxSeq
    /\ minSeq \in 1..(MaxSeq + 1)
    /\ segLo  \in 1..(MaxSeq + 1)
=============================================================================
