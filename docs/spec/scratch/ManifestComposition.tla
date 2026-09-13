--------------------------- MODULE ManifestComposition ---------------------------
(* Three writer families over one manifest: does the whole stay honest when   *)
(* every part is guarded alone?                                               *)
(*                                                                             *)
(* The manifest is a single CAS'd object carrying fields owned by different   *)
(* writers: head and the segment list (publication), checkpoint and min_seq   *)
(* (the fold), the live pack set (compaction), refs riding the log. Each      *)
(* family's own fragment is green in isolation; this fragment interleaves     *)
(* them, because the class only composition can see is CROSS-FIELD CLOBBER.   *)
(* The version-gated CAS protects a FIRST attempt by construction (token      *)
(* unchanged means base unchanged); the hazard is precisely the retry that    *)
(* refreshes its token but keeps its captured base -- it then writes every    *)
(* other family's fields as they were before the commit that beat it: a      *)
(* checkpoint erasing a seal's work, a seal reverting a fold, either          *)
(* dragging head backwards. Worse than the direct    *)
(* damage: a dragged head breaks the assumption the log-slot claim protocol   *)
(* stands on (LogSlotClaim reads the committed head to tell orphans from      *)
(* commits), so one clobber poisons a neighboring protocol's soundness. The   *)
(* fixed model clones the attempt manifest at every CAS; StaleBase* are the  *)
(* refactors that would end that.                                             *)
(*                                                                             *)
(* The oracle is a ghost history: every committing publication appends the    *)
(* truth it published. A cold start -- checkpoint refs, then the LISTED log   *)
(* tail, over the LIVE packs -- must reconstruct exactly that truth.          *)
(*                                                                             *)
(* The seal here IS a WAL publication, as in the fixed model: it claims a   *)
(* sequence, appends its COMPACT segment, advances head, and swaps the pack  *)
(* set. That is what lets a checkpoint fold ACROSS a seal's log entry and a  *)
(* second seal replan over the first one's output -- both schedules v1 of    *)
(* this fragment could not reach.                                            *)
(*                                                                             *)
(* Kept out on purpose: ambiguity/late landing (LogSlotClaim and              *)
(* BatchPublication own it per writer), object-graph depth (Closure-          *)
(* Provenance owns closure; coverage here is tip membership), a CONCURRENT    *)
(* second sealer (ClosureProvenance owns the plan-inputs clause; here seals   *)
(* are sequential replans of one actor).                                      *)

EXTENDS Naturals, FiniteSets

CONSTANTS StaleBaseCheckpoint, StaleBaseSeal, NoCpGuard, NoTipsClause

MaxSeq == 6
Seqs == 1..MaxSeq
Cps == {"c1", "c2"}
NoVal == "none"

VARIABLES
  m,        \* the manifest: [head, cpSeq, cpRefs, segs, packs, ver]
  refs,     \* the linearized truth of ref A right now
  histLen,  \* ghost: how many entries have actually committed
  histRefs, \* ghost: histRefs[s] = the truth after seq s committed
  pu,       \* the publisher:     [pc, mv, k]
  cp,       \* two checkpointers: cp[c] = [pc, mv, mySeq, myRefs, base, skips]
  se        \* the sealer: [pc, mv, planPacks, sup, out, base, refusals, sealed]
vars == <<m, refs, histLen, histRefs, pu, cp, se>>

\* Pack contents, tip-membership only: P1 carries v1; a fold output covers
\* the single value it was cut for; Qnone covers nothing.
Covers(val, packs) ==
  \/ val = NoVal
  \/ (val = "v1" /\ ({"P1", "Qv1"} \cap packs) # {})

Init ==
  /\ m = [head |-> 0, cpSeq |-> 0, cpRefs |-> NoVal, segs |-> {},
          packs |-> {}, ver |-> 0]
  /\ refs = NoVal /\ histLen = 0
  /\ histRefs = [s \in 0..MaxSeq |-> NoVal]
  /\ pu = [pc |-> "idle", mv |-> 0, k |-> 0]
  /\ cp = [c \in Cps |-> [pc |-> "idle", mv |-> 0, mySeq |-> 0,
                          myRefs |-> NoVal, base |-> m, skips |-> 0]]
  /\ se = [pc |-> "idle", mv |-> 0, planPacks |-> {}, sup |-> {},
           out |-> NoVal, base |-> m, refusals |-> 0, sealed |-> 0]

------------------------------------------------------------------------------
(* The publisher: push 1 creates A=v1 carrying its own pack P1; push 2       *)
(* deletes A. Exclusive slot creation is the floor: only the true next       *)
(* sequence can be claimed, which is what stalls publication (instead of     *)
(* silently rewriting history) once a clobbered head lies.                   *)

PuStart ==
  /\ pu.pc = "idle" /\ pu.k < 3 /\ m.head < MaxSeq
  /\ pu' = [pu EXCEPT !.pc = "armed", !.mv = m.ver]
  /\ UNCHANGED <<m, refs, histLen, histRefs, cp, se>>

PuCas ==
  /\ pu.pc = "armed" /\ m.ver = pu.mv
  /\ m.head + 1 = histLen + 1   \* the exclusive-create floor: head is honest
  /\ LET s == m.head + 1
         \* Push 1 creates A=v1 with its own pack; push 2 deletes A; push 3
         \* is the packless revival back onto v1 -- lawful whenever some
         \* live pack still carries v1, and the sharpest thing a stale cut
         \* can strand.
         newv == IF pu.k = 1 THEN NoVal ELSE "v1" IN
     /\ pu.k # 2 \/ Covers("v1", m.packs)
     /\ m' = [m EXCEPT !.head = s, !.segs = @ \cup {s}, !.ver = @ + 1,
                       !.packs = IF pu.k = 0 THEN @ \cup {"P1"} ELSE @]
     /\ refs' = newv /\ histLen' = s
     /\ histRefs' = [histRefs EXCEPT ![s] = newv]
     /\ pu' = [pu EXCEPT !.pc = "idle", !.k = @ + 1]
  /\ UNCHANGED <<cp, se>>

\* One batched submission: the delete and the revival commit through ONE
\* CAS as one multi-entry segment -- head jumps by two and no manifest ever
\* exposes the intermediate deleted state. This is process_batch draining a
\* queue, and the shape the short-body reader tripwire protects.
PuCasBatch ==
  /\ pu.pc = "armed" /\ m.ver = pu.mv /\ pu.k = 1
  /\ m.head = histLen /\ m.head + 2 <= MaxSeq
  /\ Covers("v1", m.packs)
  /\ LET s1 == m.head + 1
         s2 == m.head + 2 IN
     /\ m' = [m EXCEPT !.head = s2, !.segs = @ \cup {s1, s2}, !.ver = @ + 1]
     /\ refs' = "v1" /\ histLen' = s2
     /\ histRefs' = [histRefs EXCEPT ![s1] = NoVal, ![s2] = "v1"]
     /\ pu' = [pu EXCEPT !.pc = "idle", !.k = 3]
  /\ UNCHANGED <<cp, se>>

PuLost ==
  /\ pu.pc = "armed" /\ m.ver # pu.mv
  /\ pu' = [pu EXCEPT !.pc = "idle"]
  /\ UNCHANGED <<m, refs, histLen, histRefs, cp, se>>

------------------------------------------------------------------------------
(* Checkpointers: capture the head and refs as of now, fold through the CAS  *)
(* writing every OTHER field from the ATTEMPT manifest, trim the listed      *)
(* segments the fold absorbed. The C2 guard abandons a capture the world     *)
(* already checkpointed past. Two instances, because the original C2         *)
(* regression needs a newer fold to land between a stale capture and its     *)
(* retry. StaleBaseCheckpoint writes from the CAPTURE manifest instead;      *)
(* NoCpGuard keeps a lost capture alive across the retry.                    *)

CpCapture(c) ==
  /\ cp[c].pc = "idle" /\ m.head > m.cpSeq
  /\ cp' = [cp EXCEPT ![c].pc = "armed", ![c].mv = m.ver,
                      ![c].mySeq = m.head, ![c].myRefs = refs, ![c].base = m]
  /\ UNCHANGED <<m, refs, histLen, histRefs, pu, se>>

CpGuardSkip(c) ==
  /\ cp[c].pc = "armed" /\ ~NoCpGuard /\ m.cpSeq >= cp[c].mySeq
  /\ cp' = [cp EXCEPT ![c].pc = "idle", ![c].skips = @ + 1]
  /\ UNCHANGED <<m, refs, histLen, histRefs, pu, se>>

CpCas(c) ==
  /\ cp[c].pc = "armed" /\ m.ver = cp[c].mv
  /\ NoCpGuard \/ m.cpSeq < cp[c].mySeq
  /\ LET base == IF StaleBaseCheckpoint THEN cp[c].base ELSE m IN
     m' = [base EXCEPT !.cpSeq = cp[c].mySeq, !.cpRefs = cp[c].myRefs,
                       !.segs = {s \in base.segs : s > cp[c].mySeq},
                       !.ver = m.ver + 1]
  /\ cp' = [cp EXCEPT ![c].pc = "idle"]
  /\ UNCHANGED <<refs, histLen, histRefs, pu, se>>

\* A lost CAS retries the SAME fold with a fresh token -- the capture is
\* kept, and the C2 guard against the fresh manifest is what abandons a
\* capture the world moved past. That division of labor is the fixed
\* protocol's shape, and exactly why the guard is load-bearing.
CpLost(c) ==
  /\ cp[c].pc = "armed" /\ m.ver # cp[c].mv
  /\ cp' = [cp EXCEPT ![c].mv = m.ver]
  /\ UNCHANGED <<m, refs, histLen, histRefs, pu, se>>

------------------------------------------------------------------------------
(* The sealer: plan a cut of the current packs covering the current refs,    *)
(* seal through the CAS -- other fields from the ATTEMPT manifest, plan      *)
(* inputs proven still live, and the tips clause proving current refs stay   *)
(* covered by the result. StaleBaseSeal writes from the PLAN manifest;       *)
(* NoTipsClause lets a seal strand a ref published after its plan.           *)

SePlan ==
  /\ se.pc = "idle" /\ m.packs # {} /\ se.sealed < 2
  /\ se' = [se EXCEPT !.pc = "armed", !.mv = m.ver, !.planPacks = m.packs,
                      !.sup = m.packs,
                      !.out = IF refs = "v1" THEN "Qv1" ELSE "Qnone",
                      !.base = m]
  /\ UNCHANGED <<m, refs, histLen, histRefs, pu, cp>>

\* A committing seal claims the next sequence, appends its COMPACT segment,
\* advances head, and swaps the pack set; refs ride through unchanged.
\* StaleBaseSeal keeps the fresh claim (the slot machinery is real) but
\* writes every inherited field from the PLAN manifest: segments committed
\* since the plan vanish from the listing -- a committed delete silently
\* unlisted, which cold replay cannot see and ColdComplete catches.
SeCas ==
  /\ se.pc = "armed" /\ m.ver = se.mv
  /\ se.planPacks \subseteq m.packs
  /\ m.head = histLen /\ m.head < MaxSeq
  /\ LET result == (m.packs \ se.sup) \cup {se.out}
         s == m.head + 1 IN
     /\ NoTipsClause \/ Covers(refs, result)
     /\ LET base == IF StaleBaseSeal THEN se.base ELSE m IN
        m' = [base EXCEPT !.packs = result, !.head = s,
                          !.segs = @ \cup {s}, !.ver = m.ver + 1]
     /\ histLen' = s
     /\ histRefs' = [histRefs EXCEPT ![s] = refs]
  /\ se' = [se EXCEPT !.pc = "idle", !.sealed = @ + 1]
  /\ UNCHANGED <<refs, pu, cp>>

SeRefuse ==
  /\ se.pc = "armed" /\ m.ver = se.mv
  /\ ~NoTipsClause
  /\ ~Covers(refs, (m.packs \ se.sup) \cup {se.out})
  /\ se' = [se EXCEPT !.pc = "idle", !.refusals = @ + 1]
  /\ UNCHANGED <<m, refs, histLen, histRefs, pu, cp>>

\* A lost CAS retries the SAME plan with a fresh token; only a refusal
\* replans. The per-attempt clauses against the fresh manifest are what
\* keep a stale plan from stranding anything -- which is why removing them
\* is a mutation, not an optimization.
SeLost ==
  /\ se.pc = "armed" /\ m.ver # se.mv
  /\ se' = [se EXCEPT !.mv = m.ver]
  /\ UNCHANGED <<m, refs, histLen, histRefs, pu, cp>>

WorkNext == PuStart \/ PuCas \/ PuCasBatch \/ PuLost
        \/ (\E c \in Cps : CpCapture(c) \/ CpGuardSkip(c) \/ CpCas(c) \/ CpLost(c))
        \/ SePlan \/ SeCas \/ SeRefuse \/ SeLost

Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------------
TypeOK ==
  /\ m.head \in 0..MaxSeq /\ m.cpSeq \in 0..MaxSeq /\ m.ver \in 0..30
  /\ se.sealed \in 0..2
  /\ m.segs \subseteq Seqs /\ pu.k \in 0..3 /\ histLen \in 0..MaxSeq

\* Head never lies about how much history committed: the field a clobber
\* drags backwards, and the field every neighboring protocol trusts.
HeadTruthful == m.head = histLen

\* The checkpoint's refs are the truth as of its seq, and it never claims
\* history that has not happened.
CpTruthful ==
  /\ m.cpSeq <= histLen
  /\ m.cpSeq = 0 \/ m.cpRefs = histRefs[m.cpSeq]

\* Every seq between the checkpoint and head stays listed for replay: with
\* CpTruthful this is exactly "a cold start reconstructs the truth".
ColdComplete == \A s \in Seqs : (s > m.cpSeq /\ s <= m.head) => s \in m.segs

\* Every current ref resolves inside the live pack set.
ColdServable == Covers(refs, m.packs)

\* Witnesses (negated; each must FAIL in the fix arm): all three families
\* commit in one behavior; a fold really trims while cold stays complete; the
\* tips clause really refuses a stale cut; the C2 guard really skips a
\* superseded capture.
NoTripleCommit ==
  ~(/\ pu.k >= 2 /\ m.cpSeq > 0
    /\ ({"Qv1", "Qnone"} \cap m.packs) # {})
NoTrimmedButComplete ==
  ~(/\ m.cpSeq > 0
    /\ \E s \in Seqs : s <= m.cpSeq /\ s \notin m.segs /\ s <= m.head
    /\ \A s \in Seqs : (s > m.cpSeq /\ s <= m.head) => s \in m.segs)
NoSealRefusal == se.refusals = 0
NoGuardSkip == \A c \in Cps : cp[c].skips = 0
\* A seal really commits as a WAL publication (head moved, segment listed).
NoSealCommit == se.sealed = 0
\* The composed story in one behavior: a successful seal, a later refusal,
\* a fold, and the full push script.
NoCompositeStory ==
  ~(/\ se.sealed >= 1 /\ se.refusals >= 1 /\ m.cpSeq > 0 /\ pu.k = 3)
==================================================================================
