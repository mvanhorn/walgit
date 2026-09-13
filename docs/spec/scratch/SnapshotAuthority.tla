------------------------ MODULE SnapshotAuthority ------------------------
(* C2/C3/C7, B5/B6. Two racing import candidates at the same sequence.
   Immutable keys are abstract content identities; a seq-named hint can name
   a losing upload. Only the manifest descriptor grants read authority.
   A later checkpoint/push moves the descriptor while a multi-GET cold read
   is in flight. A warm cache survives until Crash, but is never authority.
   Hash correctness and exclusive immutable creation are environment axioms.
   Targets: snapshots.rs, log_reader.rs, checkpoint.rs, sync.rs. *)
EXTENDS Naturals, TLC
CONSTANT Fault
ASSUME Fault \in {"none", "cache", "guess", "splice"}
VARIABLES uploaded, hint, winner, revision, descriptor, phase, captured,
          floor, cache, result, crossed, readOrphanRace
vars == <<uploaded, hint, winner, revision, descriptor, phase, captured,
          floor, cache, result, crossed, readOrphanRace>>

Init ==
  /\ uploaded = {} /\ hint = 0 /\ winner = 0
  /\ revision = 0 /\ descriptor = 0
  /\ phase = "idle" /\ captured = 0 /\ floor = 0
  /\ cache = 0 /\ result = 0 /\ crossed = FALSE /\ readOrphanRace = FALSE

Upload(i) ==
  /\ i \in {1, 2} /\ i \notin uploaded
  /\ uploaded' = uploaded \cup {i}
  /\ hint' = IF hint = 0 THEN i ELSE hint
  /\ UNCHANGED <<winner, revision, descriptor, phase, captured, floor, cache,
                 result, crossed, readOrphanRace>>

(* Both imports used token 0: exactly one can publish, independently of
   which immutable was uploaded first. The other candidate stays orphaned. *)
Commit(i) ==
  /\ i \in uploaded /\ revision = 0
  /\ winner' = i /\ descriptor' = i /\ revision' = 1
  /\ UNCHANGED <<uploaded, hint, phase, captured, floor, cache, result, crossed, readOrphanRace>>

(* New committed snapshot, with distinguishable bytes at sequence 2. *)
Advance ==
  /\ revision = 1
  /\ uploaded' = uploaded \cup {3} /\ descriptor' = 3 /\ revision' = 2
  /\ UNCHANGED <<hint, winner, phase, captured, floor, cache, result, crossed, readOrphanRace>>

Begin ==
  /\ phase = "idle" /\ revision > 0
  /\ captured' = IF Fault = "cache" /\ cache # 0 THEN cache ELSE descriptor
  /\ floor' = revision /\ phase' = "data"
  /\ UNCHANGED <<uploaded, hint, winner, revision, descriptor, cache, result, crossed, readOrphanRace>>

ReadData ==
  /\ phase = "data"
  /\ LET key == CASE Fault = "guess" /\ floor = 1 -> hint
                    [] Fault = "splice" -> descriptor
                    [] OTHER -> captured
     IN /\ result' = key /\ cache' = key
  /\ crossed' = (crossed \/ floor < revision)
  /\ readOrphanRace' = (readOrphanRace \/ (floor = 1 /\ hint # winner))
  /\ phase' = "done"
  /\ UNCHANGED <<uploaded, hint, winner, revision, descriptor, captured, floor>>

Again ==
  /\ phase = "done" /\ phase' = "idle"
  /\ UNCHANGED <<uploaded, hint, winner, revision, descriptor, captured, floor,
                 cache, result, crossed, readOrphanRace>>
Crash ==
  /\ cache # 0 /\ cache' = 0
  /\ UNCHANGED <<uploaded, hint, winner, revision, descriptor, phase, captured,
                 floor, result, crossed, readOrphanRace>>
WorkNext == Advance \/ Begin \/ ReadData \/ Again \/ Crash
        \/ \E i \in {1, 2} : Upload(i) \/ Commit(i)
\* Make the stuttering already permitted by [][Next]_vars explicit to TLC.
\* This adds no behavior to Spec and does not assert progress or deadlock freedom.
Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ uploaded \subseteq {1, 2, 3} /\ hint \in 0..2 /\ winner \in 0..2
  /\ revision \in 0..2 /\ descriptor \in 0..3
  /\ phase \in {"idle", "data", "done"}
  /\ captured \in 0..3 /\ floor \in 0..2 /\ cache \in 0..3 /\ result \in 0..3
  /\ crossed \in BOOLEAN /\ readOrphanRace \in BOOLEAN
DescriptorDurable == revision > 0 => descriptor \in uploaded
SnapshotAuthority ==
  phase = "done" => result = IF floor = 1 THEN winner ELSE 3
ReadFresh ==
  phase = "data" => captured = IF floor = 1 THEN winner ELSE 3
NoCrossedRead == ~crossed
NoOrphanRaceRead == ~readOrphanRace
=============================================================================
