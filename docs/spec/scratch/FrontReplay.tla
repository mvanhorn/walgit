------------------------------- MODULE FrontReplay -------------------------------
(* C9: at-least-once transport is harmless. A front forwards receive-pack to   *)
(* the push broker and may retry the buffered body locally ONLY when it knows  *)
(* no HTTP connection was established; once delivery may have started, no      *)
(* local replay at any size (smart.rs, forward.rs).                      *)
(*                                                                             *)
(* The row's falsifier says "a duplicated POST double-applies", and the        *)
(* protocol stands on two independent legs this fragment separates:           *)
(*   1. The old-oid precondition, re-verified at every application, makes a   *)
(*      STATE-CHANGING duplicate REJECTED rather than re-applied (within the  *)
(*      contract's ABA exclusion). But a FIXED-POINT submission               *)
(*      (old = new = current) satisfies its own precondition forever: only    *)
(*      the publisher's no-op guard (a submission that changes nothing        *)
(*      publishes nothing) stops each redelivery from committing a fresh WAL  *)
(*      entry -- log growth and duplicate events with zero state change.      *)
(*      NoOpPublishes removes that guard.                                                     *)
(*   2. The front's Fallback/Indeterminate rule carries the RECEIPT. A        *)
(*      replayed ambiguous delivery can lose to its own late-landing          *)
(*      original: the client then holds a definite "rejected" while the push  *)
(*      applied. The rule never converts ambiguity into certainty -- after   *)
(*      an ambiguous delivery the client hears "outcome unknown", and a lost  *)
(*      reply IS ambiguity the client observed (its connection died without   *)
(*      an authoritative report). Commit and reply are separate steps here    *)
(*      for exactly that reason.                                              *)
(*                                                                             *)
(* Fallback fires on two signals: identity token unavailable (no connection   *)
(* attempted) and reqwest is_connect() (no connection established). The       *)
(* second is an ENVIRONMENT AXIOM borrowed from a client library's error      *)
(* taxonomy. ConnectSignalLies breaks exactly that axiom -- the classified-   *)
(* dead delivery lands inside the error-to-replay window -- and is the arm    *)
(* that proves the taxonomy is load-bearing for the receipt.                  *)
(*                                                                             *)
(* Kept out on purpose: broker-side CAS ambiguity and slot churn              *)
(* (LogSlotClaim, BatchPublication own them -- application here is one        *)
(* atomic precondition-checked step); ABA return-to-old (contract §4          *)
(* excludes it; values are monotone); bodies above the replay buffer (they    *)
(* cannot replay by construction: the 503 is the ambiguous shape minus the    *)
(* pending delivery); multi-front concurrency on DISTINCT submissions         *)
(* (ordinary CAS contention, modeled elsewhere).                              *)

EXTENDS Naturals

CONSTANTS ReplayOnAmbiguous,   \* mutation: replay the buffered body after an
                               \* ambiguous send instead of answering unknown
          ConnectSignalLies,   \* mutation: a delivery classified connect-fail
                               \* was actually delivered and lands late
          NoReplayPrecondition,\* mutation: the local replay path applies
                               \* without re-checking the declared old value
          NoOpPublishes        \* mutation: the publisher commits a WAL entry
                               \* for a submission that changes nothing

MaxTries == 3

V0 == 0
V1 == 1

VARIABLES
  ref,        \* the served ref value
  sub,        \* the submission in flight: "change" (V0 -> V1) then, after a
              \* clean success, "noop" (V1 -> V1, the fixed point)
  applied,    \* ghost: state-changing applications of the CURRENT submission
  entries,    \* ghost: WAL entries committed for the CURRENT submission
  cpc,        \* client: "send" | "ok" | "ng" | "unknown"
  fpc,        \* front: "idle" | "replay" -- a decided local replay not yet
              \* executed; the window every laundering trace needs
  rpend,      \* a committed-but-undelivered report: "none" | "ok" | "ng"
  tries,      \* client attempts consumed for the current submission
  sawUnknown, \* ghost: the client observed ambiguity at least once -- an
              \* explicit "outcome unknown" OR a reply that never arrived
  replayed,   \* ghost: a local fallback replay committed (witness anchor)
  pending     \* a sent-but-unacknowledged delivery: "none" | "inflight"

vars == <<ref, sub, applied, entries, cpc, fpc, rpend, tries, sawUnknown,
          replayed, pending>>

Init ==
  /\ ref = V0 /\ sub = "change" /\ applied = 0 /\ entries = 0
  /\ cpc = "send" /\ fpc = "idle" /\ rpend = "none" /\ tries = 0
  /\ sawUnknown = FALSE /\ replayed = FALSE /\ pending = "none"

------------------------------------------------------------------------------
(* One application against the WAL. The precondition (C3, per attempt): the   *)
(* declared old value must equal the current ref. A change both passes and    *)
(* then falsifies it; a fixed point passes it forever -- which is why the     *)
(* publisher's no-op guard, not the precondition, is what keeps a duplicated  *)
(* no-op from committing entries.                                             *)

PrecondHolds == IF sub = "change" THEN ref = V0 ELSE ref = V1

\* TRUE when this application commits a WAL entry: a change always does; a
\* fixed point only under the removed guard.
Commits == IF sub = "change" THEN TRUE ELSE NoOpPublishes

Apply(ok, notOk) ==
  IF PrecondHolds
    THEN /\ ref' = IF sub = "change" THEN V1 ELSE ref
         /\ applied' = IF sub = "change" THEN applied + 1 ELSE applied
         /\ entries' = IF Commits THEN entries + 1 ELSE entries
         /\ rpend' = ok
    ELSE /\ rpend' = notOk /\ UNCHANGED <<ref, applied, entries>>

------------------------------------------------------------------------------
(* Client attempt: the front forwards, the environment picks the fate.        *)

\* Clean forward: the broker receives and applies; the report is now pending
\* delivery -- commit and reply are DIFFERENT steps, and the reply can be
\* lost after the commit.
ForwardResponds ==
  /\ cpc = "send" /\ fpc = "idle" /\ rpend = "none" /\ tries < MaxTries
  /\ tries' = tries + 1
  /\ Apply("ok", "ng")
  /\ UNCHANGED <<sub, cpc, fpc, sawUnknown, replayed, pending>>

\* Connect-classified failure: the axiom says nothing reached the broker, so
\* the front decides to replay the buffered body locally; the replay executes
\* later. ConnectSignalLies breaks the axiom: the classified-dead delivery is
\* in flight and may land inside that window.
ForwardConnectFail ==
  /\ cpc = "send" /\ fpc = "idle" /\ rpend = "none" /\ tries < MaxTries
  /\ tries' = tries + 1
  /\ pending' = IF ConnectSignalLies THEN "inflight" ELSE pending
  /\ fpc' = "replay"
  /\ UNCHANGED <<ref, sub, applied, entries, cpc, rpend, sawUnknown, replayed>>

\* Ambiguous send: delivery may have started. The fixed front answers
\* "outcome unknown" and replays nothing; the bytes stay in flight.
\* ReplayOnAmbiguous schedules a local replay instead -- laundering.
ForwardAmbiguous ==
  /\ cpc = "send" /\ fpc = "idle" /\ rpend = "none" /\ tries < MaxTries
  /\ tries' = tries + 1
  /\ pending' = "inflight"
  /\ IF ReplayOnAmbiguous
       THEN /\ fpc' = "replay" /\ UNCHANGED <<cpc, sawUnknown>>
       ELSE /\ cpc' = "unknown" /\ sawUnknown' = TRUE /\ UNCHANGED fpc
  /\ UNCHANGED <<ref, sub, applied, entries, rpend, replayed>>

\* The decided local replay commits through the same per-attempt
\* precondition every publication uses -- unless NoReplayPrecondition strips
\* it -- and leaves its report pending delivery.
ReplayCommit ==
  /\ fpc = "replay" /\ rpend = "none"
  /\ fpc' = "idle" /\ replayed' = TRUE
  /\ IF PrecondHolds \/ NoReplayPrecondition
       THEN /\ ref' = IF sub = "change" THEN V1 ELSE ref
            /\ applied' = IF sub = "change" THEN applied + 1 ELSE applied
            /\ entries' = IF Commits \/ NoReplayPrecondition
                            THEN entries + 1 ELSE entries
            /\ rpend' = "ok"
       ELSE /\ rpend' = "ng" /\ UNCHANGED <<ref, applied, entries>>
  /\ UNCHANGED <<sub, cpc, tries, sawUnknown, pending>>

\* The pending report reaches the client...
DeliverReply ==
  /\ rpend # "none"
  /\ cpc' = rpend /\ rpend' = "none"
  /\ UNCHANGED <<ref, sub, applied, entries, fpc, tries, sawUnknown,
                 replayed, pending>>

\* ...or never does: the front crashed or the connection died after the
\* commit. The client observed ambiguity -- no authoritative report exists
\* on its side of the wire -- which is exactly what sawUnknown means.
LoseReply ==
  /\ rpend # "none"
  /\ cpc' = "unknown" /\ rpend' = "none" /\ sawUnknown' = TRUE
  /\ UNCHANGED <<ref, sub, applied, entries, fpc, tries, replayed, pending>>

\* An ambiguous or lied-about delivery lands: same precondition, and its
\* response reaches no one.
LateDelivery ==
  /\ pending = "inflight"
  /\ pending' = "none"
  /\ IF PrecondHolds
       THEN /\ ref' = IF sub = "change" THEN V1 ELSE ref
            /\ applied' = IF sub = "change" THEN applied + 1 ELSE applied
            /\ entries' = IF Commits THEN entries + 1 ELSE entries
       ELSE UNCHANGED <<ref, applied, entries>>
  /\ UNCHANGED <<sub, cpc, fpc, rpend, tries, sawUnknown, replayed>>

\* After ambiguity the client retries the same submission -- the
\* at-least-once source the protocol invites by design.
ClientRetry ==
  /\ cpc = "unknown" /\ tries < MaxTries
  /\ cpc' = "send"
  /\ UNCHANGED <<ref, sub, applied, entries, fpc, rpend, tries, sawUnknown,
                 replayed, pending>>

\* After a clean success the client pushes the fixed point: the same ref at
\* the value it already holds (old = new = current). Ghost counters reset --
\* the invariants are per submission.
StartNoOp ==
  /\ sub = "change" /\ cpc = "ok" /\ pending = "none" /\ rpend = "none"
  /\ sub' = "noop" /\ cpc' = "send" /\ tries' = 0
  /\ applied' = 0 /\ entries' = 0 /\ rpend' = "none"
  /\ UNCHANGED <<ref, fpc, sawUnknown, replayed, pending>>

WorkNext == ForwardResponds \/ ForwardConnectFail \/ ForwardAmbiguous
        \/ ReplayCommit \/ DeliverReply \/ LoseReply
        \/ LateDelivery \/ ClientRetry \/ StartNoOp

\* Make the stuttering already permitted by [][Next]_vars explicit to TLC.
\* This adds no behavior to Spec and does not assert progress or deadlock freedom.
Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------------
TypeOK ==
  /\ ref \in {V0, V1} /\ sub \in {"change", "noop"}
  /\ applied \in 0..2 /\ entries \in 0..3 /\ tries \in 0..MaxTries
  /\ cpc \in {"send", "ok", "ng", "unknown"}
  /\ fpc \in {"idle", "replay"} /\ rpend \in {"none", "ok", "ng"}
  /\ pending \in {"none", "inflight"}

\* Leg 1a: the current submission changes state at most once, whatever the
\* transport does. Carried by the precondition alone.
AtMostOnce == applied <= 1

\* Leg 1b: the current submission commits at most one WAL entry, however
\* many times it is delivered. For a fixed point the precondition is
\* powerless -- only the publisher's no-op guard keeps this true.
AtMostOneEntry == entries <= 1

\* A definite success on a state-changing submission is truthful. (A no-op's
\* ok is the expected report for publishing nothing.)
OkTruthful == (cpc = "ok" /\ sub = "change") => applied >= 1

\* Leg 2, the sharp one: a definite REJECTION while the submission applied
\* is lawful only after the client observed ambiguity -- an explicit
\* "outcome unknown" or a reply that never arrived. On any path where every
\* answer was definite, ng means not applied.
NoLaunderedRejection ==
  (cpc = "ng" /\ sub = "change" /\ applied >= 1) => sawUnknown

\* Witnesses (negated; each must FAIL in the fix arm): a local fallback
\* replay lawfully applies; recovery to applied-exactly-once after
\* ambiguity; a duplicate rejected by the precondition; the honest
\* ng-while-applied behind observed ambiguity (NoLaunderedRejection is not
\* vacuous); a no-op that reports ok while publishing nothing.
NoFallbackApply == ~(cpc = "ok" /\ applied = 1 /\ replayed)
NoAmbiguousRecovery == ~(sawUnknown /\ cpc = "ok" /\ applied = 1)
NoDuplicateRejected == ~(sub = "change" /\ applied = 1 /\ cpc = "ng")
NoHonestConfusion ==
  ~(sub = "change" /\ cpc = "ng" /\ applied = 1 /\ sawUnknown)
NoQuietNoOp == ~(sub = "noop" /\ cpc = "ok" /\ entries = 0)
==================================================================================
