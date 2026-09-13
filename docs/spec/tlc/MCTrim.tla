----------------------------- MODULE MCTrim -----------------------------
(* Focused reference harness: unlike the original pool, a delete can make
   already-published objects collectible. Check the full active-read window,
   not only ClosureLive at the latest tip. No changes to WALContract. *)
EXTENDS MC
CONSTANT Fault
ASSUME Fault \in {"none", "reader"}
TrimTxnPool ==
  { [refs |-> {rA}, old |-> (rA :> None), new |-> (rA :> v2), provides |-> {o1, o2}],
    [refs |-> {rA}, old |-> (rA :> v2), new |-> (rA :> None), provides |-> {}] }
TrimWithoutReader(S) ==
  /\ S \subseteq live /\ S # {}
  /\ S \cap Needed(Len(hist)) = {}
  /\ \A id \in DOMAIN pend : pend[id].stage = "up" => S \cap NeedOf(pend[id].txn) = {}
  /\ live' = live \ S
  /\ UNCHANGED <<hist, acked, objs, pend, nextId, rd, obs, view>>
TrimNext ==
  \/ \E c \in Clients : PushBegin(c) \/ ReadBegin(c)
  \/ \E c \in Clients, i \in Instances : ReadEnd(c, i)
  \/ \E id \in DOMAIN pend : Upload(id) \/ CommitPush(id) \/ NackPush(id) \/ AckPush(id) \/ LoseAck(id)
  \/ Fold
  \/ \E S \in SUBSET Objs : IF Fault = "reader" THEN TrimWithoutReader(S) ELSE Trim(S)
  \/ \E i \in Instances : Crash(i)
TrimSpec == Init /\ [][TrimNext]_vars
ReadCompletable ==
  \A c \in Clients : rd[c].act =>
    \A j \in rd[c].lo..Len(hist) : Needed(j) \subseteq live
NoHistoricalTrim == ProvenanceAll
=============================================================================
