-------------------------- MODULE ReadinessCarry --------------------------
(***************************************************************************)
(* One host's pack-readiness bookkeeping against one repository's manifest *)
(* history. `RepoState` keeps two counters: `revision`, the manifest        *)
(* revision whose refs the local copy reflects, and `packs_revision`, the   *)
(* revision whose pack inventory is installed. `packs_ready()` is their     *)
(* equality, and `level_satisfied(Serve)` trusts it: a ready host serves    *)
(* objects from its local packs without reconciling. Every lane that        *)
(* advances `revision` decides whether `packs_revision` follows ("carry"):  *)
(*                                                                          *)
(*   push local commit   publish.rs      PushCarry ("packs" in the code)   *)
(*   manifest edit       publish.rs      EditCarry ("packs_proven")         *)
(*   refs sync apply     sync.rs         ApplyCarry (proven inventory)     *)
(*   pack reconcile      sync.rs         stamps the manifest it worked from *)
(*   open after restart  registry.rs     OpenApplies, EmptyReady            *)
(*   handle construction handle.rs       Sentinel: packs_revision := 0      *)
(*                                                                          *)
(* The two counters prove the inventory only for the revision `revision`    *)
(* names. The model asks when a lane may trust them, and what each lane     *)
(* costs when it does not.                                                  *)
(*                                                                          *)
(* Abstractions. Pack inventories are sets of identities: a pack, or a      *)
(* side-file an annotation advertises for an installed pack (`has_rev`,     *)
(* bitmap, graph layer). Manifest edits that leave `packs` identical are    *)
(* settings publications, which also append a log entry; annotations and    *)
(* reclassifications change `packs` and append none. The reconcile always   *)
(* completes its downloads and graph maintenance (a failed pass stamps 0 in  *)
(* the code, which only adds passes). CAS contention is not modelled: a     *)
(* publication requires the publisher's held manifest to be current, and a  *)
(* stale publisher adopts the store's manifest through ApplyDelta first,    *)
(* which is what the CAS retry does. Other hosts appear only through the    *)
(* manifests they publish. Cache-root sharing between processes, torn       *)
(* files and reclaim are CacheDiscipline's and TempReclaim's subjects.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  MaxRev,         \* manifest revisions explored: 1 (creation) .. MaxRev
  Packs,          \* pack identities a push may add, each at most once
  SideFiles,      \* side-file identities an annotation may advertise
  Role,           \* "creator" (made the repository) | "opener" (met it later)
  BirthRevision,  \* the state a creator persists: 1 (its manifest) or 0 (a default state)
  Sentinel,       \* git.commit_graph: an opened handle owes one reconcile (handle.rs)
  PushCarry,      \* "packs" | "packs_proven": the push local commit's rule
  EditCarry,      \* "none" | "packs" | "packs_proven": cache_manifest_edit's rule
  ApplyCarry,     \* the "packs_proven" rule inside apply_delta as well
  OpenApplies,    \* "log": apply the loaded manifest iff applied_seq < head_seq;
                  \* "log_or_revision": also when state.revision < manifest.revision
  EmptyReady,     \* an open onto a manifest that names no packs is ready: an empty
                  \* inventory is installed in any directory (registry.rs)
  Crashes         \* whether the host may lose its process (and, on tmpfs, its disk)

ASSUME Role \in {"creator", "opener"}
ASSUME BirthRevision \in {0, 1}
ASSUME PushCarry \in {"packs", "packs_proven"}
ASSUME EditCarry \in {"none", "packs", "packs_proven"}
ASSUME Sentinel \in BOOLEAN /\ ApplyCarry \in BOOLEAN /\ Crashes \in BOOLEAN
ASSUME OpenApplies \in {"log", "log_or_revision"} /\ EmptyReady \in BOOLEAN
ASSUME MaxRev \in Nat /\ MaxRev >= 2
ASSUME Packs \cap SideFiles = {}

Items == Packs \cup SideFiles
Revs  == 0..MaxRev

VARIABLES
  rev,        \* the store's current manifest revision
  inv,        \* inv[r]: the pack inventory revision r names (inv[0] = {})
  seq,        \* head_seq: a push or a settings publication appends a log entry;
              \* an annotation or reclassification moves the revision alone
  alive,      \* the host process is up
  hManifest,  \* revision of the manifest the handle holds
  hRev,       \* RepoState.revision in memory
  hPacksRev,  \* RepoState.packs_revision in memory
  hSeq,       \* RepoState.applied_seq in memory
  installed,  \* items present in the host's pack directory (survives a crash, not a wipe)
  pRev, pPacksRev, pSeq,  \* the state file on disk
  target,     \* revision a running reconcile works from; 0 when none runs
  last,       \* which host lane acted most recently (for the waste witnesses)
  wasReady,   \* whether the counters said ready just before that lane acted
  syncRev     \* RepoState.revision when the running reconcile started

vars == <<rev, inv, seq, alive, hManifest, hRev, hPacksRev, hSeq, installed,
          pRev, pPacksRev, pSeq, target, last, wasReady, syncRev>>

Ready == hPacksRev = hRev              \* RepoState::packs_ready()
Current == alive /\ hManifest = rev    \* the CAS precondition: a current held manifest

\* A lane is about to advance `revision`; does `packs_revision` follow? Judged
\* on the state before the lane mutates it, against the inventory `newInv`
\* the new manifest names. `packs`: identical inventory and the counters say
\* ready. `packs_proven` adds: the counters describe the held revision.
Carries(rule, newInv) ==
  /\ rule # "none"
  /\ newInv = inv[hManifest]
  /\ Ready
  /\ (rule = "packs_proven" => hManifest = hRev)

Persist == /\ pRev' = hRev' /\ pPacksRev' = hPacksRev' /\ pSeq' = hSeq'

Init ==
  /\ rev = 1 /\ inv = [r \in Revs |-> {}] /\ seq = 0
  /\ installed = {} /\ target = 0 /\ last = "none" /\ wasReady = FALSE /\ syncRev = 0
  /\ IF Role = "creator"
       THEN \* Registry::create: the handle is built and used in the same process.
            \* With BirthRevision = 1 the creator keeps its saved readiness
            \* (nothing inherited, so the Sentinel is bypassed); with 0 the
            \* Sentinel's zero coincides with the default state.
            /\ alive = TRUE /\ hManifest = 1
            /\ hRev = BirthRevision /\ hPacksRev = BirthRevision /\ hSeq = 0
            /\ pRev = BirthRevision /\ pPacksRev = BirthRevision /\ pSeq = 0
       ELSE \* Someone else created it; this host has no directory yet.
            /\ alive = FALSE /\ hManifest = 0
            /\ hRev = 0 /\ hPacksRev = 0 /\ hSeq = 0
            /\ pRev = 0 /\ pPacksRev = 0 /\ pSeq = 0

-----------------------------------------------------------------------------
(* Publications by this host. Each requires a current held manifest.       *)

\* receive-pack: the pack is installed locally before the CAS; the local
\* commit advances `revision` and carries per PushCarry.
Push(p) ==
  /\ Current /\ rev < MaxRev /\ p \notin inv[rev]
  /\ rev' = rev + 1 /\ seq' = seq + 1
  /\ inv' = [inv EXCEPT ![rev + 1] = inv[rev] \cup {p}]
  /\ installed' = installed \cup {p}
  /\ hManifest' = rev + 1 /\ hRev' = rev + 1 /\ hSeq' = seq + 1
  \* The pack this push adds is the pack it installed, so the inventory clause
  \* holds by construction; what remains is whether the counters are trusted.
  /\ hPacksRev' = IF Ready /\ (PushCarry = "packs_proven" => hManifest = hRev)
                    THEN rev + 1 ELSE hPacksRev
  /\ Persist
  /\ last' = "push" /\ wasReady' = Ready /\ UNCHANGED syncRev
  /\ UNCHANGED <<alive, target>>

\* A settings publication through cache_manifest_edit: `packs` identical, and
\* a log entry, so a host that missed it applies it at open.
Edit ==
  /\ Current /\ rev < MaxRev
  /\ rev' = rev + 1 /\ seq' = seq + 1
  /\ inv' = [inv EXCEPT ![rev + 1] = inv[rev]]
  /\ hManifest' = rev + 1 /\ hRev' = rev + 1 /\ hSeq' = seq + 1
  /\ hPacksRev' = IF Carries(EditCarry, inv[rev]) THEN rev + 1 ELSE hPacksRev
  /\ UNCHANGED <<alive, installed, target>>
  /\ Persist
  /\ last' = "edit" /\ wasReady' = Ready /\ UNCHANGED syncRev

\* An annotation (or reclassification) through cache_manifest_edit: a PackRef
\* changes, so no rule carries, and no log entry is written. The annotator may
\* hold the side-file (it generated it) or not (the CLI advertises what a pack
\* ships without holding the pack).
Annotate(s) ==
  /\ Current /\ rev < MaxRev /\ s \notin inv[rev] /\ inv[rev] \cap Packs # {}
  /\ rev' = rev + 1
  /\ inv' = [inv EXCEPT ![rev + 1] = inv[rev] \cup {s}]
  /\ hManifest' = rev + 1 /\ hRev' = rev + 1
  /\ hPacksRev' = hPacksRev
  /\ installed' \in {installed, installed \cup {s}}
  /\ UNCHANGED <<seq, alive, hSeq, target>>
  /\ Persist
  /\ last' = "annotate" /\ wasReady' = Ready /\ UNCHANGED syncRev

-----------------------------------------------------------------------------
(* Publications by other hosts: the store moves, this host learns later.  *)

ExtPush(p) ==
  /\ rev < MaxRev /\ p \notin inv[rev]
  /\ rev' = rev + 1 /\ seq' = seq + 1
  /\ inv' = [inv EXCEPT ![rev + 1] = inv[rev] \cup {p}]
  /\ UNCHANGED <<alive, hManifest, hRev, hPacksRev, hSeq, installed,
                 pRev, pPacksRev, pSeq, target, last, wasReady, syncRev>>

ExtEdit ==
  /\ rev < MaxRev
  /\ rev' = rev + 1 /\ seq' = seq + 1
  /\ inv' = [inv EXCEPT ![rev + 1] = inv[rev]]
  /\ UNCHANGED <<alive, hManifest, hRev, hPacksRev, hSeq, installed,
                 pRev, pPacksRev, pSeq, target, last, wasReady, syncRev>>

ExtAnnotate(s) ==
  /\ rev < MaxRev /\ s \notin inv[rev] /\ inv[rev] \cap Packs # {}
  /\ rev' = rev + 1
  /\ inv' = [inv EXCEPT ![rev + 1] = inv[rev] \cup {s}]
  /\ UNCHANGED <<seq, alive, hManifest, hRev, hPacksRev, hSeq, installed,
                 pRev, pPacksRev, pSeq, target, last, wasReady, syncRev>>

-----------------------------------------------------------------------------
(* The host's own sync lanes.                                              *)

\* The refs sync (or a CAS retry's adopt) applies a newer manifest under
\* sync_mutex: refs first, `revision` alone; a reconcile may be running.
ApplyDelta ==
  /\ alive /\ hManifest < rev
  /\ hManifest' = rev /\ hRev' = rev /\ hSeq' = seq
  /\ hPacksRev' = IF ApplyCarry /\ Carries("packs_proven", inv[rev]) THEN rev ELSE hPacksRev
  /\ Persist
  /\ last' = "apply" /\ wasReady' = Ready /\ UNCHANGED syncRev
  /\ UNCHANGED <<rev, inv, seq, alive, installed, target>>

\* A Serve-level read finds level_satisfied false and starts the materialize
\* task under pack_mutex, working from the manifest the handle holds now.
ReconcileStart ==
  /\ alive /\ target = 0 /\ ~Ready
  /\ target' = hManifest /\ syncRev' = hRev /\ last' = "none"
  /\ UNCHANGED <<rev, inv, seq, alive, hManifest, hRev, hPacksRev, hSeq,
                 installed, pRev, pPacksRev, pSeq, wasReady>>

\* The pass installs what its manifest names and stamps that manifest's
\* revision, whatever `revision` has become meanwhile.
ReconcileEnd ==
  /\ alive /\ target # 0
  /\ installed' = installed \cup inv[target]
  /\ hPacksRev' = target
  /\ target' = 0
  /\ UNCHANGED <<rev, inv, seq, alive, hManifest, hRev, hSeq>>
  /\ Persist
  /\ last' = "reconcile" /\ wasReady' = FALSE /\ UNCHANGED syncRev

-----------------------------------------------------------------------------
(* Process life. A crash keeps the directory (a persistent cache); a wipe   *)
(* loses it (a fresh container). Registry::open then loads the current      *)
(* manifest and the state file, applies the delta when OpenApplies finds    *)
(* the saved state behind, and the constructor applies the Sentinel.        *)

Crash ==
  /\ Crashes /\ alive
  /\ alive' = FALSE /\ target' = 0 /\ last' = "none" /\ wasReady' = FALSE
  /\ UNCHANGED <<syncRev, rev, inv, seq, hManifest, hRev, hPacksRev, hSeq, installed,
                 pRev, pPacksRev, pSeq>>

Wipe ==
  /\ Crashes /\ alive
  /\ alive' = FALSE /\ target' = 0 /\ last' = "none" /\ wasReady' = FALSE
  /\ installed' = {} /\ pRev' = 0 /\ pPacksRev' = 0 /\ pSeq' = 0
  /\ UNCHANGED <<syncRev, rev, inv, seq, hManifest, hRev, hPacksRev, hSeq>>

Restart ==
  /\ ~alive
  /\ LET behind == pSeq < seq \/ (OpenApplies = "log_or_revision" /\ pRev < rev)
         stateRev == IF behind THEN rev ELSE pRev
         sentinelRev == IF Sentinel THEN 0 ELSE pPacksRev
         packsRev == IF EmptyReady /\ inv[rev] = {} THEN stateRev ELSE sentinelRev
     IN /\ alive' = TRUE /\ hManifest' = rev
        /\ hRev' = stateRev
        /\ hSeq' = IF behind THEN seq ELSE pSeq
        /\ hPacksRev' = packsRev
        \* The constructor applies the Sentinel, then apply_delta saves the state
        \* it produced; a skipped apply saves nothing. The empty-inventory rule
        \* runs after the apply and lives in memory, like the Sentinel.
        /\ pRev' = IF behind THEN rev ELSE pRev
        /\ pSeq' = IF behind THEN seq ELSE pSeq
        /\ pPacksRev' = IF behind THEN sentinelRev ELSE pPacksRev
  \* The open lane is measured like the others: the saved counters said ready.
  /\ last' = "open" /\ wasReady' = (pPacksRev = pRev)
  /\ UNCHANGED <<syncRev, rev, inv, seq, installed, target>>

-----------------------------------------------------------------------------

WorkNext ==
  \/ \E p \in Packs : Push(p) \/ ExtPush(p)
  \/ Edit \/ ExtEdit
  \/ \E s \in SideFiles : Annotate(s) \/ ExtAnnotate(s)
  \/ ApplyDelta \/ ReconcileStart \/ ReconcileEnd
  \/ Crash \/ Wipe \/ Restart

Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties.                                                             *)

TypeOK ==
  /\ rev \in 1..MaxRev /\ seq \in Nat
  /\ inv \in [Revs -> SUBSET Items] /\ inv[0] = {}
  /\ hManifest \in Revs /\ hRev \in Revs /\ hPacksRev \in Revs
  /\ pRev \in Revs /\ pPacksRev \in Revs
  /\ installed \subseteq Items /\ target \in Revs
  /\ last \in {"none", "push", "edit", "annotate", "apply", "reconcile", "open"}
  /\ wasReady \in BOOLEAN /\ syncRev \in Revs

\* Safety. Readiness is a promise about the revision `revision` names: a
\* ready host has installed everything that revision's inventory lists.
ReadyNamesInventory == (alive /\ Ready) => inv[hRev] \subseteq installed

\* Stronger: a ready host has installed what the manifest it HOLDS lists.
\* The refs sync never applies a manifest at the handle's own revision, so a
\* handle that adopted a newer manifest at open without an apply would keep
\* a state naming an older inventory for good. Holds once open applies by
\* revision as well (the `open_log_*` configurations show it failing without).
ReadyServesHeld == (alive /\ Ready) => inv[hManifest] \subseteq installed

\* Waste. Each lane's fallback is "leave packs_revision behind". A lane that
\* found the counters ready and left them not ready should have done so
\* only because the next pass has something to install. Scoped to the lane's
\* own contribution: a host already not ready before the lane acted is the
\* previous lane's cost, not this one's.
Complete == inv[hManifest] \subseteq installed
LaneNeverWastes(lane) ==
  (alive /\ last = lane /\ wasReady /\ ~Ready) => ~Complete

EditNeverWastes     == LaneNeverWastes("edit")
AnnotateNeverWastes == LaneNeverWastes("annotate")
ApplyNeverWastes    == LaneNeverWastes("apply")
\* The open lane: judged against the counters the state file held. The
\* Sentinel's pass on an inherited directory is graph maintenance the model
\* does not see, so this property is checked without it.
OpenNeverWastes     == LaneNeverWastes("open")

\* A pass that ran while `revision` stood still leaves the host ready;
\* otherwise every Serve-level read starts another pass until something
\* else moves `revision`. A pass overtaken by a push or an apply owes one
\* more pass by design (its verdict expired), and is not counted.
ReconcileSettles == (alive /\ last = "reconcile" /\ syncRev = hRev) => Ready

=============================================================================
