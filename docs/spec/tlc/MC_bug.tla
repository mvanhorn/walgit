----------------------------- MODULE MC_bug -----------------------------
(***************************************************************************)
(* NEGATIVE CONTROL. Deliberately weakened model: MCCommitPushBug is      *)
(* CommitPush WITHOUT the per-ref old-value CAS check (T4). Everything    *)
(* else is identical to MC's run (a). HistPreconds MUST fail here; a      *)
(* suite that cannot fail proves nothing. Never merge this into MC.tla.  *)
(***************************************************************************)
EXTENDS MC

MCCommitPushBug(id) ==
  /\ id \in DOMAIN pend /\ pend[id].stage = "up"
  \* BUG: per-ref old-value CAS check (T4) deleted here.
  /\ NeedOf(pend[id].txn) \subseteq live
  /\ hist' = Append(hist, [kind |-> "push", id |-> id, txn |-> pend[id].txn])
  /\ pend' = [pend EXCEPT ![id].stage = "cmt"]
  /\ UNCHANGED <<acked, objs, live, nextId, rd, obs, view>>

MCNextBug ==
  \/ \E c \in Clients : PushBegin(c) \/ ReadBegin(c)
  \/ \E c \in Clients, i \in Instances : ReadEnd(c, i)
  \/ \E id \in DOMAIN pend :
       Upload(id) \/ MCCommitPushBug(id) \/ NackPush(id)
                  \/ AckPush(id)         \/ LoseAck(id)
  \/ Fold
  \/ \E S \in TrimSets : Trim(S)
  \/ \E i \in Instances : Crash(i)

MCSpecBug == Init /\ [][MCNextBug]_vars
=============================================================================
