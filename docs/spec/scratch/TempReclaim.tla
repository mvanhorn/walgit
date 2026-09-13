----------------------------- MODULE TempReclaim -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS NoDropGuard, NoInterlock, AgeAuthority, NoDeadReclaim, NoSweep,
          MaxPid,
          MaxSeq

Procs == {"p1", "p2"}
Lanes == {"pub", "rdr"}
PC    == {"idle", "swept", "writing"}
Pids  == 1..MaxPid
Seqs  == 0..(MaxSeq - 1)
Bound == Cardinality(Procs) * Cardinality(Lanes)

Temp(x, s) == [pid |-> x, seq |-> s]

VARIABLES
  alive,
  pid,
  past,
  nextpid,
  lane,
  lseq,
  nextseq,
  inflight,
  temps,
  victim,
  cancelled,
  renamedOK,
  sweptDead,
  laneSweptDead,
  sweptPastPeer
vars == <<alive, pid, past, nextpid, lane, lseq, nextseq, inflight, temps,
          victim, cancelled, renamedOK, sweptDead, laneSweptDead, sweptPastPeer>>
ghosts == <<victim, cancelled, renamedOK, sweptDead, laneSweptDead, sweptPastPeer>>

Live(x)     == \E q \in Procs : alive[q] /\ pid[q] = x
Dead(x)     == ~Live(x)
Writing(p)  == {l \in Lanes : lane[p][l] = "writing"}
OwnedBy(x)  == {t \in temps : t.pid = x}

Reclaimable(me, reg) ==
  IF NoSweep THEN {}
  ELSE {t \in temps :
          \/ ~NoDeadReclaim /\ Dead(t.pid)
          \/ t.pid = me /\ (NoInterlock \/ t.seq \notin reg)
          \/ AgeAuthority /\ t.pid # me /\ Live(t.pid)}

Init ==
  /\ alive = [p \in Procs |-> TRUE]
  /\ pid = [p \in Procs |-> IF p = "p1" THEN 1 ELSE 2]
  /\ past = [p \in Procs |-> {}]
  /\ nextpid = 3
  /\ lane = [p \in Procs |-> [l \in Lanes |-> "idle"]]
  /\ lseq = [p \in Procs |-> [l \in Lanes |-> 0]]
  /\ nextseq = [p \in Procs |-> 0]
  /\ inflight = [p \in Procs |-> {}]
  /\ temps = {}
  /\ victim = FALSE /\ cancelled = FALSE /\ renamedOK = FALSE
  /\ sweptDead = FALSE /\ laneSweptDead = FALSE /\ sweptPastPeer = FALSE

Sweep(p, l) ==
  /\ alive[p] /\ lane[p][l] = "idle"
  /\ LET r == Reclaimable(pid[p], inflight[p]) IN
       /\ temps' = temps \ r
       /\ sweptDead' = (sweptDead \/ \E t \in r : Dead(t.pid))
       /\ laneSweptDead' = (laneSweptDead \/ \E t \in r : Dead(t.pid))
       /\ sweptPastPeer' =
            (sweptPastPeer \/ \E t \in temps \ r : t.pid # pid[p] /\ Live(t.pid))
  /\ lane' = [lane EXCEPT ![p][l] = "swept"]
  /\ UNCHANGED <<alive, pid, past, nextpid, lseq, nextseq, inflight,
                 victim, cancelled, renamedOK>>

Create(p, l) ==
  /\ alive[p] /\ lane[p][l] = "swept" /\ nextseq[p] < MaxSeq
  /\ LET s == nextseq[p] IN
       /\ temps' = temps \cup {Temp(pid[p], s)}
       /\ inflight' = [inflight EXCEPT ![p] = @ \cup {s}]
       /\ lseq' = [lseq EXCEPT ![p][l] = s]
       /\ nextseq' = [nextseq EXCEPT ![p] = s + 1]
  /\ lane' = [lane EXCEPT ![p][l] = "writing"]
  /\ UNCHANGED <<alive, pid, past, nextpid>> /\ UNCHANGED ghosts

Rename(p, l) ==
  /\ alive[p] /\ lane[p][l] = "writing"
  /\ LET t == Temp(pid[p], lseq[p][l]) IN
       /\ IF t \in temps
          THEN temps' = temps \ {t} /\ renamedOK' = TRUE /\ victim' = victim
          ELSE temps' = temps /\ victim' = TRUE /\ renamedOK' = renamedOK
       /\ inflight' = [inflight EXCEPT ![p] = @ \ {lseq[p][l]}]
  /\ lane' = [lane EXCEPT ![p][l] = "idle"]
  /\ lseq' = [lseq EXCEPT ![p][l] = 0]
  /\ UNCHANGED <<alive, pid, past, nextpid, nextseq,
                 cancelled, sweptDead, laneSweptDead, sweptPastPeer>>

Cancel(p, l) ==
  /\ alive[p] /\ lane[p][l] = "writing"
  /\ temps' = temps
  /\ IF NoDropGuard
     THEN inflight' = inflight
     ELSE inflight' = [inflight EXCEPT ![p] = @ \ {lseq[p][l]}]
  /\ cancelled' = TRUE
  /\ lane' = [lane EXCEPT ![p][l] = "idle"]
  /\ lseq' = [lseq EXCEPT ![p][l] = 0]
  /\ UNCHANGED <<alive, pid, past, nextpid, nextseq,
                 victim, renamedOK, sweptDead, laneSweptDead, sweptPastPeer>>

Crash(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ inflight' = [inflight EXCEPT ![p] = {}]
  /\ lane' = [lane EXCEPT ![p] = [l \in Lanes |-> "idle"]]
  /\ lseq' = [lseq EXCEPT ![p] = [l \in Lanes |-> 0]]
  /\ UNCHANGED <<pid, past, nextpid, nextseq, temps>> /\ UNCHANGED ghosts

Restart(p) ==
  /\ ~alive[p] /\ nextpid <= MaxPid
  /\ LET r == Reclaimable(nextpid, {}) IN
       /\ temps' = temps \ r
       /\ sweptDead' = (sweptDead \/ \E t \in r : Dead(t.pid))
       /\ sweptPastPeer' = (sweptPastPeer \/ \E t \in temps \ r : Live(t.pid))
  /\ alive' = [alive EXCEPT ![p] = TRUE]
  /\ past' = [past EXCEPT ![p] = @ \cup {pid[p]}]
  /\ pid' = [pid EXCEPT ![p] = nextpid]
  /\ nextpid' = nextpid + 1
  /\ nextseq' = [nextseq EXCEPT ![p] = 0]
  /\ UNCHANGED <<lane, lseq, inflight, victim, cancelled, renamedOK, laneSweptDead>>

WorkNext ==
  \/ \E p \in Procs, l \in Lanes :
       Sweep(p, l) \/ Create(p, l) \/ Rename(p, l) \/ Cancel(p, l)
  \/ \E p \in Procs : Crash(p) \/ Restart(p)

Next == WorkNext \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ alive \in [Procs -> BOOLEAN]
  /\ pid \in [Procs -> Pids]
  /\ past \in [Procs -> SUBSET Pids]
  /\ nextpid \in 3..(MaxPid + 1)
  /\ lane \in [Procs -> [Lanes -> PC]]
  /\ lseq \in [Procs -> [Lanes -> Seqs]]
  /\ nextseq \in [Procs -> 0..MaxSeq]
  /\ inflight \in [Procs -> SUBSET Seqs]
  /\ temps \in SUBSET [pid : Pids, seq : Seqs]

BoundedLitter == Cardinality(temps) <= Bound

NoLiveVictim == ~victim

PidsOwned ==
  /\ \A p \in Procs : pid[p] < nextpid /\ \A x \in past[p] : x < pid[p]
  /\ \A p, q \in Procs : p # q =>
       ({pid[p]} \cup past[p]) \cap ({pid[q]} \cup past[q]) = {}
  /\ \A t \in temps : \E p \in Procs : t.pid = pid[p] \/ t.pid \in past[p]

LaneShape ==
  \A p \in Procs :
    /\ inflight[p] = {lseq[p][l] : l \in Writing(p)}
    /\ Cardinality(inflight[p]) = Cardinality(Writing(p))
    /\ \A l \in Lanes : lane[p][l] = "writing" => lseq[p][l] < nextseq[p]
    /\ \A l \in Lanes : lane[p][l] # "writing" => lseq[p][l] = 0
    /\ ~alive[p] => inflight[p] = {} /\ Writing(p) = {}

Registered(p) == {Temp(pid[p], s) : s \in inflight[p]}
Leftover(p) == OwnedBy(pid[p]) \ Registered(p)
Residue ==
  \A p \in Procs :
    /\ \A x \in past[p] : OwnedBy(x) = {}
    /\ alive[p] =>
         /\ Registered(p) \subseteq OwnedBy(pid[p])
         /\ Cardinality(Leftover(p)) <= Cardinality({l \in Lanes : lane[p][l] = "idle"})
    /\ ~alive[p] => Cardinality(OwnedBy(pid[p])) <= Cardinality(Lanes)

IndInv == TypeOK /\ PidsOwned /\ LaneShape /\ Residue /\ BoundedLitter

IndInit ==
  /\ nextpid \in 3..(MaxPid + 1)
  /\ alive \in [Procs -> BOOLEAN]
  /\ pid \in [Procs -> Pids]
  /\ \A p \in Procs : pid[p] < nextpid
  /\ \A p, q \in Procs : p # q => pid[p] # pid[q]
  /\ past \in [Procs -> SUBSET Pids]
  /\ \A p \in Procs : \A x \in past[p] : x < pid[p]
  /\ \A p, q \in Procs : p # q =>
       ({pid[p]} \cup past[p]) \cap ({pid[q]} \cup past[q]) = {}
  /\ lane \in [Procs -> [Lanes -> PC]]
  /\ \A p \in Procs : ~alive[p] => Writing(p) = {}
  /\ nextseq \in [Procs -> 0..MaxSeq]
  /\ lseq \in [Procs -> [Lanes -> Seqs]]
  /\ \A p \in Procs : \A l \in Lanes :
       /\ lane[p][l] = "writing" => lseq[p][l] < nextseq[p]
       /\ lane[p][l] # "writing" => lseq[p][l] = 0
  /\ \A p \in Procs : \A l, m \in Lanes :
       l # m /\ lane[p][l] = "writing" /\ lane[p][m] = "writing" =>
         lseq[p][l] # lseq[p][m]
  /\ inflight = [p \in Procs |-> {lseq[p][l] : l \in Writing(p)}]
  /\ temps \in SUBSET [pid : Pids, seq : Seqs]
  /\ PidsOwned /\ Residue
  /\ victim = FALSE /\ cancelled = FALSE /\ renamedOK = FALSE
  /\ sweptDead = FALSE /\ laneSweptDead = FALSE /\ sweptPastPeer = FALSE

NoDeadReclaimRecovery == ~(sweptDead /\ renamedOK)

NoCancelRecovery == ~(cancelled /\ renamedOK)

NoFullOccupancy == ~(\A p \in Procs : alive[p] /\ Writing(p) = Lanes)

NoLaneReclaim == ~laneSweptDead

NoSweepPastPeer == ~sweptPastPeer
===============================================================================
