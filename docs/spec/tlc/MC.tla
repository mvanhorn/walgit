------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Bounded model-checking harness for WALContract.    *)
(* Every model-side adaptation lives HERE, never in WALContract.tla:      *)
(*   - Trim restricted to singleton sets (TrimSets) via MCNextTrim, as    *)
(*     4e prescribes ("restrict Trim to singleton S in the first model"); *)
(*   - a Trim-disabled next-state relation (MCNextNoTrim) for the T15     *)
(*     dichotomy run that adds ProvenanceAll;                             *)
(*   - concrete Reach / TxnPool values (TLC's :> and @@);                 *)
(*   - safety specs WITHOUT Fairness (the module says safety needs none), *)
(*     and MCSpecLive with the module's own Fairness for liveness;        *)
(*   - Symm for SYMMETRY on Clients/Instances (safety runs only:          *)
(*     symmetry is unsound under liveness checking).                      *)
(***************************************************************************)
EXTENDS WALContract, TLC

CONSTANTS rA, rB, v1, v2, v3, o1, o2, o3, o4, c1, c2, i1, i2

\* 4e: shared o1 exercises the trim guards.
MCReach ==
  (None :> {}) @@ (v1 :> {o1}) @@ (v2 :> {o1, o2}) @@ (v3 :> {o1, o3})

\* 4e: the 5 candidate transactions.
MCTxnPool ==
  { [refs |-> {rA},     old |-> (rA :> None),              \* create
                        new |-> (rA :> v1), provides |-> {o1}],
    [refs |-> {rA},     old |-> (rA :> v1),                \* dependent update
                        new |-> (rA :> v2), provides |-> {o2}],
    [refs |-> {rA},     old |-> (rA :> v1),                \* sibling conflict
                        new |-> (rA :> v3), provides |-> {o3}],
    [refs |-> {rB},     old |-> (rB :> None),              \* independent ref
                        new |-> (rB :> v1), provides |-> {o1}],
    [refs |-> {rA, rB}, old |-> (rA :> v1) @@ (rB :> v1),  \* multi-ref submission
                        new |-> (rA :> v2) @@ (rB :> v2), provides |-> {o2}] }

TrimSets == { {o} : o \in Objs }

MCNextTrim ==
  \/ \E c \in Clients : PushBegin(c) \/ ReadBegin(c)
  \/ \E c \in Clients, i \in Instances : ReadEnd(c, i)
  \/ \E id \in DOMAIN pend :
       Upload(id) \/ CommitPush(id) \/ NackPush(id)
                  \/ AckPush(id)    \/ LoseAck(id)
  \/ Fold
  \/ \E S \in TrimSets : Trim(S)
  \/ \E i \in Instances : Crash(i)

MCNextNoTrim ==
  \/ \E c \in Clients : PushBegin(c) \/ ReadBegin(c)
  \/ \E c \in Clients, i \in Instances : ReadEnd(c, i)
  \/ \E id \in DOMAIN pend :
       Upload(id) \/ CommitPush(id) \/ NackPush(id)
                  \/ AckPush(id)    \/ LoseAck(id)
  \/ Fold
  \/ \E i \in Instances : Crash(i)

MCSpecTrimSafety   == Init /\ [][MCNextTrim]_vars     \* run (a)
MCSpecNoTrimSafety == Init /\ [][MCNextNoTrim]_vars   \* run (b) + ProvenanceAll
MCSpecLive         == Init /\ [][MCNextTrim]_vars /\ Fairness

Symm == Permutations(Clients) \cup Permutations(Instances)
=============================================================================
