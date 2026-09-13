------------------------ MODULE BatchPublication ------------------------
(* C4/C5/C7/C8, B2/B3/B7. Two publishers, each used once; the first
   has two independent submissions. Capture/validation, upload, send, store
   CAS, response and resolution are separate steps. A timed-out request may
   land AFTER the caller has returned unknown. Checkpointing can erase the
   positive evidence without undoing the commit. No clocks or leases.

   Refinement targets: publish.rs process_batch, cas_landed and finish_unknown.
   Upload/connectivity/authorization failure is abstracted by Allowed and by
   UploadFail; this is NOT a model of the serving ODB's raw-object quarantine.
   Fault changes one guard; the oracles below never depend on Fault. *)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS Scenario, Fault
ASSUME Scenario \in {"race", "denied", "missing", "policy", "dependent", "delete", "noop", "rejectednoop"}
ASSUME Fault \in {"none", "policy", "partial", "isolation", "retry", "earlyack", "absence", "phantom", "noopphantom"}
Writers == {1, 2}
Refs == {"a", "b", "meta"}
Zero == [r \in Refs |-> 0]
Txn(rs, old, new, allowed, policy) ==
  [refs |-> rs, old |-> old, new |-> new, allowed |-> allowed, policy |-> policy]
CreateA == Txn({"a"}, 0, 1, {"a"}, -1)
CreateB == Txn({"b"}, 0, 1, {"b"}, -1)
Atomic == Txn({"a", "b"}, 0, 1, {"a", "b"}, -1)
Denied == Txn({"a", "b"}, 0, 1, {"a"}, -1)
Missing == Txn({"a", "b"}, 0, 1, {}, -1)
Policy == Txn({"meta"}, 0, 1, {"meta"}, -1)
Guarded == Txn({"a"}, 0, 1, {"a"}, 0)
Update == Txn({"a"}, 1, 2, {"a"}, -1)
Delete == Txn({"a"}, 1, 0, {"a"}, -1)
\* Fixed points: old = new. NoopAfter holds only in the OVERLAY world where
\* the batchmate's CreateA penciled a=1 -- the exact seam where a no-op's
\* receipt can outrun the commit it depends on. NoopZero holds against the
\* durable capture (delete-absent), the lawful standalone no-op.
NoopAfter == Txn({"a"}, 1, 1, {"a"}, -1)
NoopZero == Txn({"a"}, 0, 0, {"a"}, -1)
Batch(w) ==
  CASE Scenario = "race" -> IF w = 1 THEN <<Atomic, CreateB>> ELSE <<CreateA>>
    [] Scenario = "denied" -> IF w = 1 THEN <<Denied, CreateB>> ELSE <<CreateA>>
    [] Scenario = "missing" -> IF w = 1 THEN <<Missing, CreateB>> ELSE <<CreateA>>
    [] Scenario = "policy" -> IF w = 1 THEN <<Policy, Guarded>> ELSE <<Guarded>>
    [] Scenario = "dependent" -> IF w = 1 THEN <<CreateA, Update>> ELSE <<CreateB>>
    [] Scenario = "delete" -> IF w = 1 THEN <<CreateA, Delete>> ELSE <<CreateA>>
    [] Scenario = "noop" -> IF w = 1 THEN <<CreateA, NoopAfter>> ELSE <<NoopZero>>
    \* Rejected + no-op: the denied member never pencils the overlay, so the
    \* no-op classifies against captured refs and the early exit answers
    \* both -- rejection for one, ok for the other, no slot, no CAS.
    [] Scenario = "rejectednoop" -> IF w = 1 THEN <<Denied, NoopZero>> ELSE <<CreateA>>

Allowed(t, s) ==
  {r \in t.refs : r \in t.allowed /\ s[r] = t.old}
PolicyOK(t, s) == t.policy = -1 \/ s["meta"] = t.policy
Mask(t, s, fault) ==
  IF ~(PolicyOK(t, s) \/ fault = "policy") THEN {}
  ELSE IF fault = "partial" THEN Allowed(t, s)
  ELSE IF Allowed(t, s) = t.refs THEN t.refs ELSE {}
Apply(s, t, mask) == [r \in Refs |-> IF r \in mask THEN t.new ELSE s[r]]
Plan(w, s, fault) ==
  LET P[n \in 0..Len(Batch(w))] ==
        IF n = 0 THEN [state |-> s, masks |-> <<>>]
        ELSE LET t == Batch(w)[n]
                 m == Mask(t, P[n-1].state, fault)
             IN [state |-> Apply(P[n-1].state, t, m),
                 masks |-> Append(P[n-1].masks, m)]
      p == P[Len(Batch(w))]
  IN IF fault = "isolation" /\ {} \in {p.masks[n] : n \in DOMAIN p.masks}
     THEN [state |-> s, masks |-> [n \in DOMAIN p.masks |-> {}]] ELSE p
Accepted(p) == UNION {p.masks[n] : n \in DOMAIN p.masks} # {}
\* A no-op submission: accepted with a full mask AND changing nothing.
IsNoop(w, p, n) ==
  /\ p.masks[n] = Batch(w)[n].refs
  /\ Batch(w)[n].old = Batch(w)[n].new
HasNoop(w, p) == \E n \in DOMAIN p.masks : IsNoop(w, p, n)
\* Every accepted submission is a no-op: the publisher's early exit --
\* report ok, claim no slot, CAS nothing (process_batch's all-no-op path).
AllNoop(w, p) ==
  /\ Accepted(p)
  /\ \A n \in DOMAIN p.masks : p.masks[n] # {} => IsNoop(w, p, n)

VARIABLES refs, rev, history, evidence, phase, base, token, plan, uploaded,
          wire, report, retried, late, folded, noopok
vars == <<refs, rev, history, evidence, phase, base, token, plan, uploaded,
          wire, report, retried, late, folded, noopok>>
Init ==
  /\ refs = Zero /\ rev = 0 /\ history = <<>> /\ evidence = {}
  /\ phase = [w \in Writers |-> "capture"]
  /\ base = [w \in Writers |-> Zero] /\ token = [w \in Writers |-> 0]
  /\ plan = [w \in Writers |-> Plan(w, Zero, "none")]
  /\ uploaded = {} /\ wire = [w \in Writers |-> "none"]
  /\ report = [w \in Writers |-> "none"]
  /\ retried = {} /\ late = {} /\ folded = {} /\ noopok = {}

Capture(w) ==
  /\ phase[w] = "capture"
  /\ base' = [base EXCEPT ![w] = refs]
  /\ token' = [token EXCEPT ![w] = rev]
  /\ plan' = [plan EXCEPT ![w] = Plan(w, refs, Fault)]
  /\ phase' = [phase EXCEPT ![w] = "prepared"]
  /\ UNCHANGED <<refs, rev, history, evidence, uploaded, wire, report, retried, late, folded, noopok>>

Reject(w) ==
  /\ phase[w] = "prepared" /\ ~Accepted(plan[w])
  /\ phase' = [phase EXCEPT ![w] = "done"]
  /\ report' = [report EXCEPT ![w] = "ng"]
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, wire, retried, late, folded, noopok>>

Upload(w) ==
  /\ phase[w] = "prepared" /\ Accepted(plan[w]) /\ ~AllNoop(w, plan[w])
  /\ uploaded' = uploaded \cup {w}
  /\ phase' = [phase EXCEPT ![w] = "send"]
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, wire, report, retried, late, folded, noopok>>

UploadFail(w) ==
  /\ phase[w] = "prepared" /\ Accepted(plan[w]) /\ ~AllNoop(w, plan[w])
  /\ phase' = [phase EXCEPT ![w] = "done"]
  /\ report' = [report EXCEPT ![w] = "ng"]
  /\ noopok' = IF Fault = "noopphantom" /\ HasNoop(w, plan[w])
                 THEN noopok \cup {w} ELSE noopok
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, wire, retried, late, folded>>

\* The all-no-op early exit: every ACCEPTED submission already holds, so the
\* publisher answers ok and touches neither slot nor CAS. Rejected members
\* may coexist (they never pencil the overlay and get their definitive
\* rejection); only a batch with an accepted PUBLISHING member skips this
\* path.
NoopSettle(w) ==
  /\ phase[w] = "prepared" /\ AllNoop(w, plan[w])
  /\ phase' = [phase EXCEPT ![w] = "done"]
  /\ report' = [report EXCEPT ![w] = "ok"]
  /\ noopok' = noopok \cup {w}
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, wire, retried, late, folded>>

Send(w) ==
  /\ phase[w] = "send"
  /\ wire' = [wire EXCEPT ![w] = "pending"]
  /\ phase' = [phase EXCEPT ![w] = "wait"]
  /\ report' = [report EXCEPT ![w] = IF Fault = "earlyack" THEN "ok" ELSE @]
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, retried, late, folded, noopok>>

Land(w) ==
  /\ wire[w] = "pending" /\ token[w] = rev
  /\ refs' = plan[w].state /\ rev' = rev + 1
  /\ history' = Append(history, [writer |-> w, before |-> refs,
        after |-> plan[w].state, masks |-> plan[w].masks, durable |-> w \in uploaded])
  /\ evidence' = evidence \cup {w}
  /\ wire' = [wire EXCEPT ![w] = "committed"]
  /\ late' = IF report[w] = "unknown" THEN late \cup {w} ELSE late
  /\ UNCHANGED <<phase, base, token, plan, uploaded, report, retried, folded, noopok>>

Conflict(w) ==
  /\ wire[w] = "pending" /\ token[w] # rev
  /\ wire' = [wire EXCEPT ![w] = "conflict"]
  /\ UNCHANGED <<refs, rev, history, evidence, phase, base, token, plan, uploaded, report, retried, late, folded, noopok>>

Reply(w) ==
  /\ phase[w] = "wait" /\ wire[w] = "committed"
  /\ phase' = [phase EXCEPT ![w] = "done"]
  /\ report' = [report EXCEPT ![w] = "ok"]
  /\ noopok' = IF HasNoop(w, plan[w]) THEN noopok \cup {w} ELSE noopok
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, wire, retried, late, folded>>

Retry(w) ==
  /\ phase[w] = "wait" /\ wire[w] = "conflict"
  /\ phase' = [phase EXCEPT ![w] = IF Fault = "retry" THEN "send" ELSE "capture"]
  /\ token' = [token EXCEPT ![w] = IF Fault = "retry" THEN rev ELSE @]
  /\ wire' = [wire EXCEPT ![w] = "none"]
  /\ retried' = retried \cup {w}
  /\ UNCHANGED <<refs, rev, history, evidence, base, plan, uploaded, report, late, folded, noopok>>

Timeout(w) ==
  /\ phase[w] = "wait"
  /\ phase' = [phase EXCEPT ![w] = "resolve"]
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, wire, report, retried, late, folded, noopok>>

Resolve(w) ==
  /\ phase[w] = "resolve"
  /\ phase' = [phase EXCEPT ![w] = "done"]
  /\ report' = [report EXCEPT ![w] =
       IF w \in evidence THEN "ok" ELSE IF Fault = "absence" THEN "ng" ELSE "unknown"]
  /\ noopok' = IF HasNoop(w, plan[w])
                    /\ (w \in evidence \/ Fault = "noopphantom")
                 THEN noopok \cup {w} ELSE noopok
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, wire, retried, late, folded>>

Crash(w) ==
  /\ phase[w] # "done"
  /\ phase' = [phase EXCEPT ![w] = "done"]
  /\ report' = [report EXCEPT ![w] = "crashed"]
  /\ noopok' = IF Fault = "noopphantom" /\ phase[w] # "capture"
                    /\ HasNoop(w, plan[w])
                 THEN noopok \cup {w} ELSE noopok
  /\ UNCHANGED <<refs, rev, history, evidence, base, token, plan, uploaded, wire, retried, late, folded>>

Fold ==
  /\ evidence # {}
  /\ folded' = folded \cup evidence /\ evidence' = {} /\ rev' = rev + 1
  /\ UNCHANGED <<refs, history, phase, base, token, plan, uploaded, wire, report, retried, late, noopok>>

Work(w) == Capture(w) \/ Reject(w) \/ Upload(w) \/ UploadFail(w) \/ Send(w)
           \/ NoopSettle(w) \/ Reply(w) \/ Retry(w) \/ Resolve(w)
Deliver(w) == Land(w) \/ Conflict(w)
WorkNext == Fold \/ \E w \in Writers : Work(w) \/ Deliver(w) \/ Timeout(w) \/ Crash(w)
Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
LiveSpec == Spec /\ \A w \in Writers : WF_vars(Work(w)) /\ WF_vars(Deliver(w))
(* Healthy store/process arm: failures above may terminate everyone without a
   winner, so termination alone is NOT global progress. Here upload failure
   and process crash are absent; lost replies and finite contention remain. *)
HealthyWork(w) == Capture(w) \/ Reject(w) \/ Upload(w) \/ Send(w)
                  \/ NoopSettle(w) \/ Reply(w) \/ Retry(w) \/ Resolve(w)
HealthyWorkNext == Fold \/ \E w \in Writers : HealthyWork(w) \/ Deliver(w) \/ Timeout(w)
HealthyNext == HealthyWorkNext \/ UNCHANGED vars
HealthySpec == Init /\ [][HealthyNext]_vars
  /\ \A w \in Writers : WF_vars(HealthyWork(w)) /\ WF_vars(Deliver(w))

Committed == {history[n].writer : n \in DOMAIN history}
TypeOK ==
  /\ refs \in [Refs -> 0..2] /\ rev \in 0..4 /\ Len(history) <= 2
  /\ evidence \subseteq Writers /\ uploaded \subseteq Writers
  /\ phase \in [Writers -> {"capture", "prepared", "send", "wait", "resolve", "done"}]
  /\ base \in [Writers -> [Refs -> 0..2]] /\ token \in [Writers -> 0..4]
  /\ wire \in [Writers -> {"none", "pending", "committed", "conflict"}]
  /\ report \in [Writers -> {"none", "ok", "ng", "unknown", "crashed"}]
  /\ retried \subseteq Writers /\ late \subseteq Writers /\ folded \subseteq Writers
  /\ noopok \subseteq Writers
  /\ \A w \in Writers : plan[w].state \in [Refs -> 0..2]
       /\ plan[w].masks \in [1..Len(Batch(w)) -> SUBSET Refs]

SubmissionAtomic ==
  \A w \in Writers : \A n \in DOMAIN plan[w].masks :
    plan[w].masks[n] \in {{}, Batch(w)[n].refs}
DecisionIsolation ==
  \A w \in Writers : plan[w] = Plan(w, base[w], "none")
CommitPreconditions ==
  \A n \in DOMAIN history :
    LET h == history[n] IN h.masks = Plan(h.writer, h.before, "none").masks
NoLostUpdate ==
  \A n \in DOMAIN history :
    LET h == history[n] IN h.after = Plan(h.writer, h.before, "none").state
WriteAhead == \A n \in DOMAIN history : history[n].durable
(* "ok" is receipt of the batch result, not an ok for every submitted ref.
   The response's masks must name exactly the refs that actually committed;
   invalid independent members report no successful refs (V1 regression). *)
ReportedMasks(w) ==
  IF Fault = "phantom" THEN [n \in 1..Len(Batch(w)) |-> Batch(w)[n].refs]
  ELSE plan[w].masks
ReportsTruthful ==
  /\ \A w \in Writers : report[w] = "ok" /\ ~AllNoop(w, plan[w]) =>
       \E n \in DOMAIN history : history[n].writer = w /\ history[n].masks = ReportedMasks(w)
  /\ \A w \in Writers : report[w] = "ng" => w \notin Committed
(* The batch seam: a no-op's ok receipt is lawful in exactly two worlds --
   its whole batch was no-ops classified against this writer's own captured
   refs (the early exit), or the batch whose overlay classified it actually
   COMMITTED. A definitive ok for a no-op whose batchmate's write never
   landed is a receipt for a world that never existed (the noopphantom
   fault, i.e., failure paths special-casing no-op members as successes). *)
NoopReceiptTruthful ==
  \A w \in noopok : AllNoop(w, plan[w]) \/ w \in Committed
AtMostOnce == Cardinality(Committed) = Len(history)
Terminates == \A w \in Writers : <>(phase[w] = "done")
EventuallyCommitted == <>(Committed # {})
TransportSettles == \A w \in Writers : wire[w] = "pending" ~> wire[w] # "pending"

(* Reachability probes: the runner expects each negated witness to FAIL.
   These are existential schedule tests, not additional safety guarantees. *)
NoRetryCommit == ~(Committed \cap retried # {})
NoLateCommit == late = {}
NoFoldedUnknown == ~\E w \in folded : report[w] = "unknown"
NoAtomicCommit == ~\E n \in DOMAIN history :
  \E m \in DOMAIN history[n].masks : Cardinality(history[n].masks[m]) = 2
NoIsolatedCommit == ~\E n \in DOMAIN history :
  history[n].writer = 1 /\ history[n].masks = <<{}, {"b"}>>
NoDependentCommit == ~\E n \in DOMAIN history :
  history[n].writer = 1 /\ history[n].masks = <<{"a"}, {"a"}>>
\* The rider: a no-op ok'd together with its batchmate's committed write.
NoNoopRide == ~\E w \in noopok : w \in Committed
\* The early exit: a no-op ok'd with no commit anywhere in its history.
NoQuietBatchNoop == ~\E w \in noopok : w \notin Committed
\* The rejected+noop early exit: a no-op ok'd from a batch that also carried
\* a rejected (empty-mask) member.
NoRejectedNoopSettle == ~\E w \in noopok :
  \E n \in DOMAIN plan[w].masks : plan[w].masks[n] = {}
=============================================================================
