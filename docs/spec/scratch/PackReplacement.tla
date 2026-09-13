------------------------- MODULE PackReplacement -------------------------
(* C6/C10: a conserving cut validates ALL captured indexed links, not
   just reachable roots, before compression. It conserves those indexed OIDs
   at seal. Explicit pruning validates only the roots it deliberately retains.
   A push may land at every stage; retry refreshes the manifest/token but MUST
   NOT extend supersedes to packs the candidate never processed.

   Each abstract pack contributes distinct OIDs, and output choice exhausts
   every subset of the captured inputs. Hashes/compression/filesystem layout
   are outside the model. Closure is raw direct-link closure (not bitmap
   success). Public targets: pack_segments producer and WAL replacement seal. No production guard is inferred solely
   from this set-level abstraction. *)
EXTENDS Naturals, TLC
CONSTANTS Broken, Mode, Fault
ASSUME Broken \in BOOLEAN /\ Mode \in {"conserve", "prune"}
ASSUME Fault \in {"none", "raw", "conserve", "replace", "supersedes"}
Universe == 1..5
Links(o) == CASE o = 1 -> {2} [] o = 3 /\ Broken -> {4}
                [] o = 5 -> {1} [] OTHER -> {}
Closed(os) == \A o \in os : Links(o) \subseteq os
Reach(t) == IF t = 1 THEN {1, 2} ELSE {1, 2, 5}
VARIABLES live, tip, rev, phase, input, root, token, output, durable,
          ran, rejected, sealed, beforeSeal, retried, raced
vars == <<live, tip, rev, phase, input, root, token, output, durable,
          ran, rejected, sealed, beforeSeal, retried, raced>>
Retained == IF Mode = "prune" THEN Reach(root) ELSE input
Init ==
  /\ live = {1, 2, 3} /\ tip = 1 /\ rev = 0 /\ phase = "capture"
  /\ input = {} /\ root = 1 /\ token = 0 /\ output = {} /\ durable = {}
  /\ ran = FALSE /\ rejected = FALSE /\ sealed = FALSE
  /\ beforeSeal = {} /\ retried = FALSE /\ raced = FALSE
Capture ==
  /\ phase = "capture" /\ input' = live /\ root' = tip /\ token' = rev
  /\ phase' = "admit"
  /\ UNCHANGED <<live, tip, rev, output, durable, ran, rejected, sealed, beforeSeal, retried, raced>>
Admit ==
  /\ phase = "admit"
  /\ Closed(Retained) \/ Fault = "raw"
  /\ phase' = "compress" /\ ran' = TRUE
  /\ UNCHANGED <<live, tip, rev, input, root, token, output, durable,
                 rejected, sealed, beforeSeal, retried, raced>>
RejectInput ==
  /\ phase = "admit" /\ ~Closed(Retained) /\ Fault # "raw"
  /\ phase' = "done" /\ rejected' = TRUE
  /\ UNCHANGED <<live, tip, rev, input, root, token, output, durable,
                 ran, sealed, beforeSeal, retried, raced>>
Compress(os) ==
  /\ phase = "compress" /\ os \subseteq input
  /\ output' = os /\ phase' = "verify"
  /\ UNCHANGED <<live, tip, rev, input, root, token, durable, ran,
                 rejected, sealed, beforeSeal, retried, raced>>
OutputOK ==
  /\ Closed(output)
  /\ (IF Fault = "conserve" THEN Reach(root) ELSE Retained) \subseteq output
Verify ==
  /\ phase = "verify"
  /\ phase' = IF OutputOK THEN "upload" ELSE "done"
  /\ rejected' = ~OutputOK
  /\ UNCHANGED <<live, tip, rev, input, root, token, output, durable,
                 ran, sealed, beforeSeal, retried, raced>>
Upload ==
  /\ phase = "upload" /\ durable' = output /\ phase' = "seal"
  /\ UNCHANGED <<live, tip, rev, input, root, token, output, ran,
                 rejected, sealed, beforeSeal, retried, raced>>
Push ==
  /\ tip = 1 /\ tip' = 5 /\ live' = live \cup {5} /\ rev' = rev + 1
  /\ UNCHANGED <<phase, input, root, token, output, durable, ran,
                 rejected, sealed, beforeSeal, retried, raced>>
Retry ==
  /\ phase = "seal" /\ token # rev
  /\ token' = rev /\ retried' = TRUE
  /\ input' = IF Fault = "supersedes" THEN live ELSE input
  /\ UNCHANGED <<live, tip, rev, phase, root, output, durable, ran,
                 rejected, sealed, beforeSeal, raced>>
Seal ==
  /\ phase = "seal" /\ token = rev
  /\ beforeSeal' = live
  /\ live' = IF Fault = "replace" THEN output ELSE (live \ input) \cup output
  /\ sealed' = TRUE /\ phase' = "done" /\ rev' = rev + 1
  /\ raced' = (tip # root)
  /\ UNCHANGED <<tip, input, root, token, output, durable, ran, rejected, retried>>
WorkNext == Capture \/ Admit \/ RejectInput \/ Verify \/ Upload \/ Push \/ Retry \/ Seal
        \/ \E os \in SUBSET Universe : Compress(os)
\* Make the stuttering already permitted by [][Next]_vars explicit to TLC.
\* This adds no behavior to Spec and does not assert progress or deadlock freedom.
Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
TypeOK ==
  /\ live \subseteq Universe /\ input \subseteq Universe /\ output \subseteq Universe
  /\ durable \subseteq Universe /\ beforeSeal \subseteq Universe
  /\ tip \in {1, 5} /\ root \in {1, 5} /\ rev \in 0..2 /\ token \in 0..2
  /\ phase \in {"capture", "admit", "compress", "verify", "upload", "seal", "done"}
  /\ ran \in BOOLEAN /\ rejected \in BOOLEAN /\ sealed \in BOOLEAN
  /\ retried \in BOOLEAN /\ raced \in BOOLEAN
AdmissionSound == ran => Closed(Retained)
Conserves == sealed /\ Mode = "conserve" => beforeSeal \subseteq live
Servable == Reach(tip) \subseteq live
WriteAhead == sealed => output \subseteq durable
OutputClosed == sealed => Closed(live)
NoSeal == ~sealed
NoRejectedInput == ~(rejected /\ ~ran)
NoRacingSeal == ~(sealed /\ raced)
NoRetrySeal == ~(sealed /\ retried)
=============================================================================
