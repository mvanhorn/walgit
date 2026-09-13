------------------------- MODULE ClosureProvenance -------------------------
(* C6a: candidate boundary and current tips must be covered at every CAS.
   A hypothetical pruning replacement tests the dual seal obligation. Public
   maintenance conserves indexed objects; pruning is not a supported mode.
   The model is a bounded counterexample laboratory, not a Rust refinement
   proof. Each fault and witness is listed in tlc/cases.tsv. *)
EXTENDS Naturals

CONSTANTS PGuard, MGuard, TipGuard, StaleRetry, Cutters, PlanInputsLive

Objs == {"B0", "X", "Y", "C"}
Parent == [o \in Objs |-> CASE o = "B0" -> {}
                            [] o = "X"  -> {"B0"}
                            [] o = "Y"  -> {"B0"}
                            [] o = "C"  -> {"X"}]

ClosureOf == [o \in Objs |-> CASE o = "B0" -> {"B0"}
                               [] o = "X"  -> {"X", "B0"}
                               [] o = "Y"  -> {"Y", "B0"}
                               [] o = "C"  -> {"C", "X", "B0"}]

Packs == {"KBase", "KX", "KY", "PC", "KP"}
Holds == [p \in Packs |-> CASE p = "KBase" -> {"B0"}
                            [] p = "KX"    -> {"X"}
                            [] p = "KY"    -> {"Y"}
                            [] p = "PC"    -> {"C"}
                            [] p = "KP"    -> {"B0", "Y"}]
Objects(ps) == UNION {Holds[p] : p \in ps}

ExtRefs(p) == (UNION {Parent[o] : o \in Holds[p]}) \ Holds[p]

VARIABLES
  live,      
  disk,      
  refA,      
  refB,      
  gen,       
  pphase,    
  pcap,      
  pevid,     
  retried,   
  plan,      
  planSup,   
  replanned, 
  undercut   
vars == <<live, disk, refA, refB, gen, pphase, pcap, pevid, retried,
          plan, planSup, replanned, undercut>>

RefOids == {refA} \cup (IF refB = "unset" THEN {} ELSE {refB})
ReachableFromRefs == UNION {ClosureOf[o] : o \in RefOids}
MemberNow == ExtRefs("PC") \subseteq Objects(live \cup {"PC"})

Init == /\ live = {"KBase", "KX"} /\ disk = {"KBase", "KX"}
        /\ refA = "X" /\ refB = "unset" /\ gen = 0
        /\ pphase = "idle" /\ pcap = 0 /\ pevid = "unset" /\ retried = FALSE
        /\ plan = [c \in Cutters |-> "none"] /\ planSup = [c \in Cutters |-> {}]
        /\ replanned = FALSE /\ undercut = FALSE

Validate ==
  /\ pphase = "idle"
  /\ LET readable == ExtRefs("PC") \subseteq Objects(disk \cup {"PC"})
     IN /\ pphase' = IF readable /\ (PGuard # "validate" \/ MemberNow)
                     THEN "ready" ELSE "refused"
        /\ pevid' = IF PGuard = "attempt" THEN "unset" ELSE "ok"
  /\ UNCHANGED <<live, disk, refA, refB, gen, pcap, retried,
                 plan, planSup, replanned, undercut>>

Arm ==
  /\ pphase \in {"ready", "lost"}
  /\ pcap' = gen
  /\ pevid' = IF PGuard = "attempt" /\ ~(StaleRetry /\ pphase = "lost")
              THEN (IF MemberNow THEN "ok" ELSE "bad")
              ELSE pevid
  /\ pphase' = "armed"
  /\ UNCHANGED <<live, disk, refA, refB, gen, retried,
                 plan, planSup, replanned, undercut>>

FireCAS ==
  /\ pphase = "armed"
  /\ IF gen # pcap
     THEN /\ pphase' = "lost" /\ retried' = TRUE
          /\ UNCHANGED <<live, disk, refA, refB, gen, pcap, pevid,
                         plan, planSup, replanned, undercut>>
     ELSE IF pevid = "bad" \/ refB # "unset"
     THEN /\ pphase' = "refused"
          /\ UNCHANGED <<live, disk, refA, refB, gen, pcap, pevid, retried,
                         plan, planSup, replanned, undercut>>
     ELSE /\ pphase' = "done"
          /\ live' = live \cup {"PC"} /\ disk' = disk \cup {"PC"}
          /\ refB' = "C" /\ gen' = gen + 1
          /\ UNCHANGED <<refA, pcap, pevid, retried, plan, planSup, replanned, undercut>>

ForcePush ==
  /\ refA = "X"
  /\ refA' = "Y" /\ live' = live \cup {"KY"} /\ disk' = disk \cup {"KY"}
  /\ gen' = gen + 1
  /\ UNCHANGED <<refB, pphase, pcap, pevid, retried, plan, planSup, replanned, undercut>>

RevivePush ==
  /\ refB = "unset"
  /\ TipGuard => "X" \in Objects(live)
  /\ refB' = "X" /\ gen' = gen + 1
  /\ UNCHANGED <<live, disk, refA, pphase, pcap, pevid, retried,
                 plan, planSup, replanned, undercut>>

PlanPrune(c) ==
  /\ plan[c] = "none" /\ "KX" \in live /\ "X" \notin ReachableFromRefs
  /\ plan' = [plan EXCEPT ![c] = "ready"]
  /\ planSup' = [planSup EXCEPT ![c] = live]
  /\ UNCHANGED <<live, disk, refA, refB, gen, pphase, pcap, pevid, retried,
                 replanned, undercut>>

SealPrune(c) ==
  /\ plan[c] = "ready"
  /\ LET result == (live \ planSup[c]) \cup {"KP"}
         
         
         
         inputsLive == planSup[c] \subseteq live
         closedNow == \A o \in RefOids : ClosureOf[o] \subseteq Objects(result)
         commits == /\ (PlanInputsLive => inputsLive)
                    /\ (MGuard = "stale" \/ closedNow)
     IN /\ undercut' = (undercut \/ ~inputsLive)
        /\ plan' = [plan EXCEPT ![c] = "none"]
        /\ planSup' = [planSup EXCEPT ![c] = {}]
        /\ IF commits
           THEN /\ live' = result /\ disk' = disk \cup {"KP"}
                /\ gen' = gen + 1
                /\ UNCHANGED <<refA, refB, pphase, pcap, pevid, retried, replanned>>
           ELSE /\ replanned' = TRUE
                /\ UNCHANGED <<live, disk, refA, refB, gen, pphase, pcap, pevid,
                               retried>>

LocalDelete ==
  /\ "KX" \in disk /\ "KX" \notin live
  /\ disk' = disk \ {"KX"}
  /\ UNCHANGED <<live, refA, refB, gen, pphase, pcap, pevid, retried,
                 plan, planSup, replanned, undercut>>

WorkNext == Validate \/ Arm \/ FireCAS \/ ForcePush \/ RevivePush \/ LocalDelete
        \/ \E c \in Cutters : PlanPrune(c) \/ SealPrune(c)
\* Make the stuttering already permitted by [][Next]_vars explicit to TLC.
\* This adds no behavior to Spec and does not assert progress or deadlock freedom.
Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

TypeOK == /\ live \subseteq Packs /\ disk \subseteq Packs
          /\ refA \in {"X", "Y"} /\ refB \in {"unset", "C", "X"}
          /\ gen \in 0..5 /\ pcap \in 0..5
          /\ pphase \in {"idle", "ready", "armed", "lost", "done", "refused"}
          /\ pevid \in {"unset", "ok", "bad"}
          /\ retried \in BOOLEAN /\ replanned \in BOOLEAN
          /\ plan \in [Cutters -> {"none", "ready"}]
          /\ planSup \in [Cutters -> SUBSET Packs]
          /\ undercut \in BOOLEAN

ServableClosure == \A o \in RefOids : ClosureOf[o] \subseteq Objects(live)

LiveClosed == \A o \in Objects(live) : Parent[o] \subseteq Objects(live)

NoRefusal     == pphase # "refused"
NoCommit      == pphase # "done"
NoRetryCommit == ~(retried /\ pphase = "done")
NoReplan      == ~replanned

NoUndercut    == ~undercut
=============================================================================
