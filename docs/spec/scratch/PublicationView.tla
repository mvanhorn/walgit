------------------------- MODULE PublicationView -------------------------
EXTENDS Naturals
CONSTANT Fix
VARIABLES value, token, candidate, expected, phase, lost
vars == <<value, token, candidate, expected, phase, lost>>

Init == /\ value = 0 /\ token = 0 /\ candidate = 0 /\ expected = 0
        /\ phase = "start" /\ lost = FALSE

\* A local sync/cache apply advances the protected value and its version.
Advance == /\ value = 0 /\ value' = 1 /\ token' = 1
           /\ UNCHANGED <<candidate, expected, phase, lost>>

ReadValue == /\ phase = "start"
             /\ candidate' = value
             /\ expected' = IF Fix THEN token ELSE expected
             /\ phase' = IF Fix THEN "cas" ELSE "version"
             /\ UNCHANGED <<value, token, lost>>

ReadVersion == /\ phase = "version"
               /\ expected' = token /\ phase' = "cas"
               /\ UNCHANGED <<value, token, candidate, lost>>

\* The version check alone cannot save a candidate captured from older state.
CAS == /\ phase = "cas" /\ expected = token
       /\ lost' = (candidate # value) /\ phase' = "done"
       /\ UNCHANGED <<value, token, candidate, expected>>

WorkNext == Advance \/ ReadValue \/ ReadVersion \/ CAS
\* Make the stuttering already permitted by [][Next]_vars explicit to TLC.
\* This adds no behavior to Spec and does not assert progress or deadlock freedom.
Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
NoLostUpdate == ~lost
=============================================================================
