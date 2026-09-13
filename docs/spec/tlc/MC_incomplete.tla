-------------------------- MODULE MC_incomplete --------------------------
(* Boundary counterexample, NOT a production regression. WALContract permits
   provides={} in its assumptions but has no missing-object rejection action.
   Its fairness cannot enable CommitPush or NackPush for this request. Never
   cite the original finite valid pool's liveness pass as universal liveness.
   BatchPublication's missing scenario models the required refusal instead. *)
EXTENDS MC
IncompleteTxnPool ==
  {[refs |-> {rA}, old |-> (rA :> None), new |-> (rA :> v1), provides |-> {}]}
=============================================================================
