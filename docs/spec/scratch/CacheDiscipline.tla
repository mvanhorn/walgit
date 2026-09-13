---------------------------- MODULE CacheDiscipline ----------------------------

EXTENDS Naturals, TLC

CONSTANTS TrustPresence, NoIdentity, SkipReprove, FailOpen, NoCancelCleanup,
          SweepEntrySnap, SecondProcess, NoReaderRederive, NoRecheck

MaxAttempt == 2
MaxMver == 4
MaxTear == 1
LitterBound == 1

Contents == {"absent", "valid", "torn", "garbage"}

VARIABLES
  inst,
  cach,
  linked,
  live,
  mver,
  pub,
  swp,
  rdr,
  tears,
  litter,
  cancelled,
  viable,
  blamed,
  okevid,
  swept
vars == <<inst, cach, linked, live, mver, pub, swp, rdr, tears, litter,
          cancelled, viable, blamed, okevid, swept>>

SetInst(c) == inst' = c /\ cach' = (IF linked THEN c ELSE cach)
SetCach(c) == cach' = c /\ inst' = (IF linked THEN c ELSE inst)

IsEvidence(c) == c = "valid" \/ (NoIdentity /\ c = "torn")
HaveEvidence == IsEvidence(inst) \/ IsEvidence(cach)

RepairSatisfied == IF TrustPresence
                   THEN inst # "absent" \/ cach # "absent"
                   ELSE HaveEvidence

Init ==
  /\ inst = "absent" /\ cach = "absent" /\ linked = FALSE
  /\ live = FALSE /\ mver = 0
  /\ pub = [pc |-> "idle", mv |-> 0, attempt |-> 0, tcap |-> 0]
  /\ swp = [pc |-> "idle", mv |-> 0, lv |-> FALSE]
  /\ rdr = [pc |-> "idle", sawAbsent |-> FALSE]
  /\ tears = 0 /\ litter = 0 /\ cancelled = FALSE
  /\ viable = FALSE /\ blamed = FALSE /\ okevid = "absent" /\ swept = FALSE

AddPack ==
  /\ ~live /\ mver < MaxMver
  /\ live' = TRUE /\ mver' = mver + 1
  /\ UNCHANGED <<inst, cach, linked, pub, swp, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

RetirePack ==
  /\ live /\ mver < MaxMver
  /\ live' = FALSE /\ mver' = mver + 1
  /\ UNCHANGED <<inst, cach, linked, pub, swp, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

Prefetch ==
  /\ live /\ inst # "valid"
  /\ inst' = "valid" /\ cach' = "valid" /\ linked' = TRUE
  /\ UNCHANGED <<live, mver, pub, swp, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

Tear ==
  /\ tears < MaxTear
  /\ \/ (inst # "absent" /\ SetInst("torn") /\ UNCHANGED linked)
     \/ (inst # "absent" /\ SetInst("garbage") /\ UNCHANGED linked)
     \/ (cach # "absent" /\ SetCach("torn") /\ UNCHANGED linked)
     \/ (cach # "absent" /\ SetCach("garbage") /\ UNCHANGED linked)
  /\ tears' = tears + 1
  /\ UNCHANGED <<live, mver, pub, swp, rdr, litter, viable, blamed, okevid,
                 swept, cancelled>>

PStart ==
  /\ pub.pc \in {"idle", "done", "refused"} /\ live
  /\ pub.attempt < MaxAttempt
  /\ pub' = [pub EXCEPT !.pc = "prove", !.mv = mver, !.attempt = @ + 1,
                        !.tcap = tears]
  /\ UNCHANGED <<inst, cach, linked, live, mver, swp, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

FirstOpen == IF inst \in {"valid", "torn"} THEN inst ELSE cach

ProveStep(from) ==
  /\ pub.pc = from
  /\ IF HaveEvidence
     THEN IF NoIdentity /\ FirstOpen = "torn"
          THEN /\ pub' = [pub EXCEPT !.pc = "refused"]
               /\ blamed' = TRUE
               /\ UNCHANGED <<viable, okevid>>
          ELSE /\ pub' = [pub EXCEPT !.pc = "cas"]
               /\ okevid' = "valid"
               /\ UNCHANGED <<viable, blamed>>
     ELSE IF from = "prove"
     THEN /\ pub' = [pub EXCEPT !.pc = "repair"]
          /\ UNCHANGED <<viable, blamed, okevid>>
     ELSE /\ pub' = [pub EXCEPT !.pc = "refuse"]
          /\ UNCHANGED <<viable, blamed, okevid>>
  /\ UNCHANGED <<inst, cach, linked, live, mver, swp, rdr, tears, litter,
                 swept, cancelled>>

PProve == ProveStep("prove")

PRepairSkip ==
  /\ pub.pc = "repair" /\ RepairSatisfied
  /\ pub' = [pub EXCEPT !.pc = IF SkipReprove THEN "refuse" ELSE "reprove"]
  /\ UNCHANGED <<inst, cach, linked, live, mver, swp, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

PRepairDownload ==
  /\ pub.pc = "repair" /\ ~RepairSatisfied
  /\ cach' = "valid" /\ linked' = FALSE /\ inst' = inst
  /\ pub' = [pub EXCEPT !.pc = "reprove"]
  /\ UNCHANGED <<live, mver, swp, rdr, tears, litter, viable, blamed, okevid,
                 swept, cancelled>>

PCancel ==
  /\ pub.pc = "repair" /\ ~RepairSatisfied
  /\ litter' = IF NoCancelCleanup THEN litter + 1 ELSE litter
  /\ cancelled' = TRUE
  /\ pub' = [pub EXCEPT !.pc = "refused"]
  /\ UNCHANGED <<inst, cach, linked, live, mver, swp, rdr, tears,
                 viable, blamed, okevid, swept>>

PReprove == ProveStep("reprove")

PRefuse ==
  /\ pub.pc = "refuse"
  /\ LET restart == ~NoRecheck /\ pub.mv # mver IN
     IF FailOpen
     THEN /\ pub' = [pub EXCEPT !.pc = "cas"]
          /\ okevid' = "absent"
          /\ viable' = viable
     ELSE IF restart
     THEN /\ pub' = [pub EXCEPT !.pc = "idle"]
          /\ viable' = viable /\ okevid' = okevid
     ELSE

          /\ pub' = [pub EXCEPT !.pc = "refused"]
          /\ viable' = (viable \/ (pub.mv = mver /\ tears = pub.tcap))
          /\ okevid' = okevid
  /\ UNCHANGED <<inst, cach, linked, live, mver, swp, rdr, tears, litter,
                 blamed, swept, cancelled>>

PCas ==
  /\ pub.pc = "cas"
  /\ IF pub.mv = mver
     THEN /\ mver' = mver + 1
          /\ pub' = [pub EXCEPT !.pc = "done"]
     ELSE /\ mver' = mver
          /\ pub' = [pub EXCEPT !.pc = "idle"]
  /\ UNCHANGED <<inst, cach, linked, live, swp, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

SweepCapture ==
  /\ swp.pc = "idle"
  /\ swp' = [swp EXCEPT !.pc = "armed", !.mv = mver, !.lv = live]
  /\ UNCHANGED <<inst, cach, linked, live, mver, pub, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

SweepUnlink ==
  /\ swp.pc = "armed" /\ cach # "absent"
  /\ LET deadByCapture == ~swp.lv
         deadNow == ~live
         authority == IF SweepEntrySnap \/ SecondProcess
                      THEN deadByCapture ELSE deadNow
     IN /\ authority
        /\ cach' = "absent" /\ linked' = FALSE /\ inst' = inst
  /\ swp' = [swp EXCEPT !.pc = "idle"]
  /\ swept' = TRUE
  /\ UNCHANGED <<live, mver, pub, rdr, tears, litter, cancelled, viable, blamed,
                 okevid>>

SweepDisarm ==
  /\ swp.pc = "armed"
  /\ swp' = [swp EXCEPT !.pc = "idle"]
  /\ UNCHANGED <<inst, cach, linked, live, mver, pub, rdr, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

RProbe ==
  /\ rdr.pc = "idle" /\ live
  /\ rdr' = [rdr EXCEPT !.pc = "load", !.sawAbsent = (cach = "absent")]
  /\ UNCHANGED <<inst, cach, linked, live, mver, pub, swp, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

RLoad ==
  /\ rdr.pc = "load"
  /\ IF rdr.sawAbsent /\ cach = "absent"
     THEN /\ cach' = "valid" /\ linked' = FALSE /\ inst' = inst
          /\ rdr' = [rdr EXCEPT !.pc = "serving"]
     ELSE IF cach \in {"valid", "torn"}
     THEN /\ rdr' = [rdr EXCEPT !.pc = "serving"]
          /\ UNCHANGED <<inst, cach, linked>>
     ELSE IF NoReaderRederive
     THEN /\ rdr' = [rdr EXCEPT !.pc = "failed"]
          /\ UNCHANGED <<inst, cach, linked>>
     ELSE
          /\ cach' = "valid" /\ linked' = FALSE /\ inst' = inst
          /\ rdr' = [rdr EXCEPT !.pc = "serving"]
  /\ UNCHANGED <<live, mver, pub, swp, tears, litter, viable, blamed, okevid,
                 swept, cancelled>>

RDone ==
  /\ rdr.pc \in {"serving", "failed"}
  /\ rdr' = [rdr EXCEPT !.pc = "idle", !.sawAbsent = FALSE]
  /\ UNCHANGED <<inst, cach, linked, live, mver, pub, swp, tears, litter,
                 viable, blamed, okevid, swept, cancelled>>

WorkNext ==
  \/ AddPack \/ RetirePack \/ Prefetch \/ Tear
  \/ PStart \/ PProve \/ PRepairSkip \/ PRepairDownload \/ PCancel
  \/ PReprove \/ PRefuse \/ PCas
  \/ SweepCapture \/ SweepUnlink \/ SweepDisarm
  \/ RProbe \/ RLoad \/ RDone

Next == WorkNext \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ inst \in Contents /\ cach \in Contents /\ linked \in BOOLEAN
  /\ (linked => inst = cach)
  /\ live \in BOOLEAN /\ mver \in 0..(MaxMver + MaxAttempt + 1)
  /\ pub.pc \in {"idle", "prove", "repair", "reprove", "refuse", "cas",
                 "done", "refused"}
  /\ litter \in 0..MaxAttempt

NoFalseCovered == pub.pc \in {"cas", "done"} => okevid = "valid"

ClassificationHonest == ~blamed

NoViableVictim == ~viable

BoundedLitter == litter <= LitterBound

ReaderCompletes == rdr.pc # "failed"

NoPrefetchRescue ==
  ~(pub.pc = "done" /\ linked)

NoSweepDuringRepair ==
  ~(swept /\ pub.pc \in {"repair", "reprove"})

NoCancelRecovery == ~(cancelled /\ pub.pc = "done")
=================================================================================
