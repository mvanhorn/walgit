------------------------------ MODULE LogSlotClaim ------------------------------
(* The log-slot claim protocol: who may delete a log segment, when, and what   *)
(* bytes a committed manifest's descriptor actually resolves to                *)
(* (publish.rs: claim_log_slot / sweep_burned / drop_own_slot / cas_landed).   *)
(*                                                                             *)
(* Every publication claims `log/<seq>.pb` by exclusive create BEFORE its      *)
(* manifest CAS. Contenders finding an occupied seq with an unmoved head       *)
(* declare an orphan after a grace and BURN the seq; the winner CAS-deletes    *)
(* its burned orphans only AFTER its own commit. A lost CAS deletes the        *)
(* writer's own segment at the exact version it wrote. An ambiguous CAS        *)
(* resolves by re-reading and, on "not listed", LEAVES THE SEGMENT IN PLACE    *)
(* -- the write may still land late.                                           *)
(*                                                                             *)
(* Presence is not the whole property. The store contract's axioms include     *)
(* at-least-once delivery (a conditional DELETE can arrive twice, late) and    *)
(* S3-shaped version ABA (the token is the content hash, so byte-identical     *)
(* re-creates alias old delete tokens). A publisher whose retried segment is   *)
(* byte-identical can then lose its re-create to its own first attempt's       *)
(* stale delete, a competitor can re-create the key with different bytes, and  *)
(* the publisher's late-landing CAS commits a manifest whose descriptor        *)
(* resolves to someone else's entries: cold replay forks from what the warm    *)
(* writer acknowledged (C3). The portable guard is BYTE UNIQUENESS PER         *)
(* ATTEMPT -- a fresh nonce in every attempt's frame -- which un-aliases the   *)
(* delete tokens on any store; incarnation-unique versions (GCS generations)   *)
(* make the store immune regardless.                                           *)
(*                                                                             *)
(* Toggles, all named for the wrong implementation they model:                 *)
(*   BurnedAcrossRetry  -- keep the burned list when the own CAS loses.        *)
(*   SweepEarly         -- sweep burned orphans before the own commit.         *)
(*   DropOnAmbiguous    -- delete the own segment after "not listed".          *)
(*   StoreABA           -- versions are content hashes (S3), not fresh         *)
(*                         incarnations (GCS); deletes may deliver twice,      *)
(*                         late.                                               *)
(*   DeterministicBytes -- retried attempts re-encode identical bytes (no      *)
(*                         per-attempt nonce).                                 *)
(* The fix arm holds the first three off and survives StoreABA because bytes   *)
(* are attempt-unique; StoreABA + DeterministicBytes reproduces the fork.      *)
(*                                                                             *)
(* Abstractions: content is (writer, attempt); a version is that content       *)
(* under StoreABA, else a fresh incarnation counter. Head-preserving manifest  *)
(* edits (pack reclassification) bump the CAS token without touching the log,  *)
(* which is what hands a retried publisher the same sequence twice. Writers    *)
(* restart after walking away (a new request on the same or another host).     *)
(* Entry semantics, packs and refs stay out of scope.                          *)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS BurnedAcrossRetry, SweepEarly, DropOnAmbiguous, StoreABA,
          DeterministicBytes

Writers == {"a", "b"}
MaxSeq == 3
Seqs == 1..MaxSeq
MaxBurn == 2
MaxAttempt == 2
NoSeg == [w |-> "none", n |-> 0]

Content(x, attempt) ==
  IF DeterministicBytes THEN [w |-> x, n |-> 1] ELSE [w |-> x, n |-> attempt]

VARIABLES
  seg,      \* seg[s]: NoSeg or the content sitting at log/<s>
  incarn,   \* incarn[s]: creates ever done at log/<s> (fresh-version stores)
  head,     \* manifest head_seq
  listedc,  \* the committed descriptors: seq -> content the CAS's writer wrote
  mver,     \* manifest CAS token
  pdel,     \* in-flight conditional deletes: {[s, ver, left]} with left <= 2
  wr        \* per-writer state machine
vars == <<seg, incarn, head, listedc, mver, pdel, wr>>

\* A version under ABA is the content itself (byte hash); otherwise the
\* incarnation number -- unique per create, so stale tokens can never match.
VerOf(s, c) == IF StoreABA THEN c ELSE [w |-> "i", n |-> incarn[s]]

Init ==
  /\ seg = [s \in Seqs |-> NoSeg]
  /\ incarn = [s \in Seqs |-> 0]
  /\ head = 0 /\ listedc = <<>> /\ mver = 0 /\ pdel = {}
  /\ wr = [x \in Writers |->
       [pc |-> "idle", mv |-> 0, seq |-> 0, attempt |-> 0, ver |-> NoSeg,
        burned |-> {}, retried |-> FALSE, ambig |-> FALSE, crashed |-> FALSE]]

Listed == DOMAIN listedc

\* Capture the publication view; also how a walked-away or finished writer
\* comes back as a fresh request.
Start(x) ==
  /\ wr[x].pc \in {"idle", "gone", "done"} /\ head < MaxSeq
  /\ wr[x].attempt < MaxAttempt
  /\ wr' = [wr EXCEPT ![x].pc = "probe", ![x].mv = mver,
                      ![x].seq = head + 1, ![x].burned = {}, ![x].ambig = FALSE]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver, pdel>>

\* Exclusive create: this attempt's bytes land at the key.
ClaimFree(x) ==
  /\ wr[x].pc = "probe" /\ seg[wr[x].seq] = NoSeg
  /\ LET c == Content(x, wr[x].attempt + 1) IN
     /\ seg' = [seg EXCEPT ![wr[x].seq] = c]
     /\ incarn' = [incarn EXCEPT ![wr[x].seq] = @ + 1]
     /\ wr' = [wr EXCEPT ![x].pc = "armed", ![x].attempt = @ + 1,
                         ![x].ver = IF StoreABA THEN c
                                    ELSE [w |-> "i", n |-> incarn[wr[x].seq] + 1]]
  /\ UNCHANGED <<head, listedc, mver, pdel>>

\* Occupied with the head moved past it: someone committed. Restart the whole
\* claim against a fresh view; the burned list dies with the old call.
Contended(x) ==
  /\ wr[x].pc = "probe" /\ seg[wr[x].seq] # NoSeg /\ head >= wr[x].seq
  /\ head < MaxSeq
  /\ wr' = [wr EXCEPT ![x].mv = mver, ![x].seq = head + 1, ![x].burned = {}]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver, pdel>>

\* Occupied with the head unmoved: an orphan (crashed, or mid-flight -- the
\* probe cannot tell). Burn: remember the version for a post-commit delete.
Burn(x) ==
  /\ wr[x].pc = "probe" /\ seg[wr[x].seq] # NoSeg /\ head < wr[x].seq
  /\ wr[x].seq < MaxSeq /\ Cardinality(wr[x].burned) < MaxBurn
  /\ wr' = [wr EXCEPT
       ![x].burned = @ \cup {<<wr[x].seq, VerOf(wr[x].seq, seg[wr[x].seq])>>},
       ![x].seq = @ + 1]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver, pdel>>

\* The manifest CAS wins: the token is current, the descriptor now binds this
\* writer's bytes at this seq.
CasOk(x) ==
  /\ wr[x].pc = "armed" /\ mver = wr[x].mv
  /\ head' = wr[x].seq /\ mver' = mver + 1
  /\ listedc' = listedc @@ (wr[x].seq :> Content(x, wr[x].attempt))
  /\ wr' = [wr EXCEPT ![x].pc = "sweep"]
  /\ UNCHANGED <<seg, incarn, pdel>>

\* Post-commit sweep: SEND a conditional delete per burned orphan. Deletes are
\* at-least-once: each may deliver up to twice, arbitrarily late. SweepEarly
\* runs this while still armed -- before the own commit proved anything.
SweepAt(x, pc) ==
  /\ wr[x].pc = pc
  /\ pdel' = pdel \cup {[s |-> b[1], ver |-> b[2], left |-> 2] : b \in wr[x].burned}
  /\ wr' = [wr EXCEPT ![x].pc = IF pc = "sweep" THEN "done" ELSE "armed",
                      ![x].burned = {}]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver>>

Sweep(x) == IF SweepEarly THEN SweepAt(x, "armed") ELSE SweepAt(x, "sweep")

\* A conditional delete delivers: it removes the segment only at the exact
\* version it was issued against -- which under ABA can alias a byte-identical
\* re-create. Duplicates and late delivery are the store's prerogative.
DeliverDelete ==
  \E d \in pdel :
    /\ seg' = IF seg[d.s] # NoSeg /\ VerOf(d.s, seg[d.s]) = d.ver
              THEN [seg EXCEPT ![d.s] = NoSeg] ELSE seg
    /\ pdel' = (pdel \ {d}) \cup
               (IF d.left > 1 THEN {[d EXCEPT !.left = 1]} ELSE {})
    /\ UNCHANGED <<incarn, head, listedc, mver, wr>>

\* The manifest CAS loses: someone committed since the capture. Send the
\* conditional delete of the OWN segment (exact version) and start over
\* against a fresh view; the burned list is discarded with the failed attempt.
CasLost(x) ==
  /\ wr[x].pc = "armed" /\ mver # wr[x].mv
  /\ head < MaxSeq /\ wr[x].attempt < MaxAttempt
  /\ pdel' = pdel \cup {[s |-> wr[x].seq, ver |-> wr[x].ver, left |-> 2]}
  /\ wr' = [wr EXCEPT ![x].pc = "probe", ![x].mv = mver,
                      ![x].seq = head + 1, ![x].retried = TRUE,
                      ![x].burned = IF BurnedAcrossRetry THEN @ ELSE {}]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver>>

\* A head-preserving manifest edit (pack reclassification): the CAS token
\* moves, the log does not -- which is what hands a retrying publisher the
\* same sequence twice.
ManifestEdit ==
  /\ mver < 6
  /\ mver' = mver + 1
  /\ UNCHANGED <<seg, incarn, head, listedc, pdel, wr>>

\* The CAS reply is lost while the write may still be in flight; the writer
\* resolves, the store may land the write whenever the token is still current
\* -- including after the writer crashed or walked away.
CasAmbiguous(x) ==
  /\ wr[x].pc = "armed"
  /\ wr' = [wr EXCEPT ![x].pc = "resolve", ![x].ambig = TRUE]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver, pdel>>

LandLate(x) ==
  /\ wr[x].ambig /\ mver = wr[x].mv
  /\ head' = wr[x].seq /\ mver' = mver + 1
  /\ listedc' = listedc @@ (wr[x].seq :> Content(x, wr[x].attempt))
  /\ UNCHANGED <<seg, incarn, pdel, wr>>

ResolveListed(x) ==
  /\ wr[x].pc = "resolve" /\ wr[x].seq \in Listed
  /\ wr' = [wr EXCEPT ![x].pc = "sweep"]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver, pdel>>

\* Not listed: the write may STILL land -- leave the segment alone and walk
\* away. DropOnAmbiguous sends the own delete here; the late landing then
\* commits a descriptor over a hole.
ResolveNotListed(x) ==
  /\ wr[x].pc = "resolve" /\ wr[x].seq \notin Listed
  /\ pdel' = IF DropOnAmbiguous
             THEN pdel \cup {[s |-> wr[x].seq, ver |-> wr[x].ver, left |-> 2]}
             ELSE pdel
  /\ wr' = [wr EXCEPT ![x].pc = "gone"]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver>>

\* A crash at any seam. The segment, the pending deletes, and -- crucially --
\* an in-flight manifest CAS all outlive the process: LandLate stays enabled
\* for a crashed-while-armed writer, because the store does not know or care
\* that the sender died.
Crash(x) ==
  /\ wr[x].pc \in {"probe", "armed", "sweep", "resolve"}
  /\ wr' = [wr EXCEPT ![x].pc = "gone",
                      ![x].ambig = @ \/ wr[x].pc = "armed",
                      ![x].crashed = TRUE]
  /\ UNCHANGED <<seg, incarn, head, listedc, mver, pdel>>

WorkNext ==
  \/ DeliverDelete \/ ManifestEdit
  \/ \E x \in Writers :
       Start(x) \/ ClaimFree(x) \/ Contended(x) \/ Burn(x) \/ CasOk(x)
       \/ Sweep(x) \/ CasLost(x) \/ CasAmbiguous(x) \/ LandLate(x)
       \/ ResolveListed(x) \/ ResolveNotListed(x) \/ Crash(x)

Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ head \in 0..MaxSeq /\ mver \in 0..9
  /\ \A s \in Seqs : incarn[s] \in 0..4
  /\ \A x \in Writers : wr[x].pc \in {"idle", "probe", "armed", "sweep",
                                      "resolve", "done", "gone"}

\* Replay from any committed manifest finds every listed segment...
CommittedSegmentsPresent == \A s \in Listed : seg[s] # NoSeg

\* ...and finds the BYTES the committing writer's descriptor meant. A present
\* key holding another attempt's or another writer's entries is a fork between
\* what was acknowledged and what a cold start replays.
CommittedSegmentsMatch == \A s \in Listed : seg[s] = listedc[s]

\* Reachability witnesses (negated; each must FAIL in the fix arm).
NoOrphanSwept ==
  ~(\E x \in Writers : wr[x].pc = "done"
      /\ \E s \in Seqs : incarn[s] # 0 /\ seg[s] = NoSeg /\ s \notin Listed)
NoRetryCommit == ~(\E x \in Writers : wr[x].retried /\ wr[x].pc = "done")
NoAmbiguousCommit == ~(\E x \in Writers : wr[x].ambig /\ wr[x].seq \in Listed)
NoCrashLateCommit ==
  ~(\E x \in Writers : wr[x].crashed /\ wr[x].ambig /\ wr[x].seq \in Listed)
==================================================================================
