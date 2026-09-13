--------------------------- MODULE PackCoverage ---------------------------
(* C6/C10, B2/B6. A topic group subtracts a base group. Coverage
   names exact immutable members and a pinned generation, not a watermark.
   Prepare -> CAS/retry races retirement, reclassification, policy and tip
   changes. Fetch captures once; later maintenance cannot splice its view.

   Set membership abstracts verified raw OIDs/indexes. Pack bytes are retained
   for in-flight reads (C10b ASSUMPTION, not a proof of the GC policy). Preparing
   a certificate proves its physical group's objects; the dependency bundle
   and dynamic residual must reconstruct the requested closure. No Git wire,
   hashing, traversal, delta encoding or download implementation is modeled.
   Public targets: WAL coverage binding and server packfile_uri selection. *)
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Fault
ASSUME Fault \in {"none", "retire", "scope", "policy", "generation", "dependency", "companion"}
Packs == {"A", "D", "B", "C", "M", "R"}
Bytes == [p \in Packs |-> CASE p = "A" -> {"a"} [] p = "D" -> {"d"}
  [] p = "B" -> {"b"} [] p = "C" -> {"c"} [] p = "M" -> {"m"}
  [] OTHER -> {"b", "c"}]
Objects(ps) == UNION {Bytes[p] : p \in ps}
Roots(epoch) == IF epoch = 1 THEN {"a", "b"} ELSE {"a", "b", "c", "d"}
Own(epoch) == IF epoch = 1 THEN {"b"} ELSE {"b", "c"}
BaseMembers(epoch) == IF epoch = 1 THEN {"A"} ELSE {"A", "D"}
TopicMembers(epoch, inventory) ==
  IF epoch = 1 THEN {"B"} ELSE IF "C" \in inventory THEN {"B", "C"} ELSE {"B", "R"}
EmptyProof == [epoch |-> 0, policy |-> 0, members |-> {}]

VARIABLES live, scope, policy, head, rev, base2, retired, reclassified,
          phase, token, candidate, certificate, bindingOK, retried,
          fetch, captured, offered, residual, needed, scopedOffer,
          oldTipOffer, retryBind, crossed
vars == <<live, scope, policy, head, rev, base2, retired, reclassified,
          phase, token, candidate, certificate, bindingOK, retried,
          fetch, captured, offered, residual, needed, scopedOffer,
          oldTipOffer, retryBind, crossed>>
View == [live |-> live, scope |-> scope, policy |-> policy, head |-> head,
         base2 |-> base2, proof |-> certificate, rev |-> rev]
MemberScope(ps, inventory, scopes) ==
  ps \subseteq inventory /\ \A p \in ps : scopes[p] = "code"

Init ==
  /\ live = Packs \ {"R"}
  /\ scope = [p \in Packs |-> IF p = "M" THEN "meta" ELSE "code"]
  /\ policy = 0 /\ head = 1 /\ rev = 0 /\ base2 = FALSE
  /\ retired = FALSE /\ reclassified = FALSE
  /\ phase = "prepare" /\ token = 0 /\ candidate = EmptyProof
  /\ certificate = EmptyProof /\ bindingOK = TRUE /\ retried = FALSE
  /\ fetch = "idle" /\ captured = View
  /\ offered = {} /\ residual = {} /\ needed = {} /\ scopedOffer = TRUE
  /\ oldTipOffer = FALSE /\ retryBind = FALSE /\ crossed = FALSE

Prepare ==
  /\ phase = "prepare" /\ policy = 0
  /\ LET members == TopicMembers(head, live) IN
       /\ MemberScope(members, live, scope)
       /\ Own(head) \subseteq Objects(members)
       /\ candidate' = [epoch |-> head, policy |-> policy, members |-> members]
  /\ token' = rev /\ phase' = "publish"
  /\ UNCHANGED <<live, scope, policy, head, rev, base2, retired, reclassified,
       certificate, bindingOK, retried, fetch, captured, offered, residual,
       needed, scopedOffer, oldTipOffer, retryBind, crossed>>

(* The proof's policy is the captured policy. A global settings change may
   leave a stored certificate stale: it must NOT become eligible for fetch.
   Member disappearance/scope changes, however, reject the binding itself. *)
Bind ==
  /\ phase = "publish" /\ token = rev
  /\ candidate.members \subseteq live \/ Fault = "retire"
  /\ (\A p \in candidate.members : scope[p] = "code") \/ Fault = "scope"
  /\ certificate' = candidate /\ phase' = "done" /\ rev' = rev + 1
  /\ bindingOK' = MemberScope(candidate.members, live, scope)
  /\ retryBind' = retried
  /\ UNCHANGED <<live, scope, policy, head, base2, retired, reclassified,
       token, candidate, retried, fetch, captured, offered, residual,
       needed, scopedOffer, oldTipOffer, crossed>>

Retry ==
  /\ phase = "publish" /\ token # rev
  /\ token' = rev /\ retried' = TRUE
  /\ UNCHANGED <<live, scope, policy, head, rev, base2, retired, reclassified,
       phase, candidate, certificate, bindingOK, fetch, captured, offered,
       residual, needed, scopedOffer, oldTipOffer, retryBind, crossed>>

(* Retirement conserves objects and retains old bytes. Reclassification
   invalidates membership, not the immutable content-addressed bytes. *)
Retire ==
  /\ ~retired /\ retired' = TRUE /\ live' = (live \ {"C"}) \cup {"R"}
  /\ rev' = rev + 1
  /\ UNCHANGED <<scope, policy, head, base2, reclassified, phase, token,
       candidate, certificate, bindingOK, retried, fetch, captured, offered,
       residual, needed, scopedOffer, oldTipOffer, retryBind, crossed>>
Reclassify ==
  /\ ~reclassified /\ reclassified' = TRUE
  /\ scope' = [scope EXCEPT !["C"] = "meta"] /\ rev' = rev + 1
  /\ UNCHANGED <<live, policy, head, base2, retired, phase, token, candidate,
       certificate, bindingOK, retried, fetch, captured, offered, residual,
       needed, scopedOffer, oldTipOffer, retryBind, crossed>>
ChangePolicy ==
  /\ policy = 0 /\ policy' = 1 /\ rev' = rev + 1
  /\ UNCHANGED <<live, scope, head, base2, retired, reclassified, phase, token,
       candidate, certificate, bindingOK, retried, fetch, captured, offered,
       residual, needed, scopedOffer, oldTipOffer, retryBind, crossed>>
Push ==
  /\ head = 1 /\ head' = 2 /\ rev' = rev + 1
  /\ UNCHANGED <<live, scope, policy, base2, retired, reclassified, phase,
       token, candidate, certificate, bindingOK, retried, fetch, captured,
       offered, residual, needed, scopedOffer, oldTipOffer, retryBind, crossed>>
BaseProof ==
  /\ head = 2 /\ ~base2 /\ base2' = TRUE /\ rev' = rev + 1
  /\ UNCHANGED <<live, scope, policy, head, retired, reclassified, phase,
       token, candidate, certificate, bindingOK, retried, fetch, captured,
       offered, residual, needed, scopedOffer, oldTipOffer, retryBind, crossed>>

Capture ==
  /\ fetch = "idle" /\ captured' = View /\ fetch' = "select"
  /\ UNCHANGED <<live, scope, policy, head, rev, base2, retired, reclassified,
       phase, token, candidate, certificate, bindingOK, retried, offered,
       residual, needed, scopedOffer, oldTipOffer, retryBind, crossed>>

Select ==
  /\ fetch = "select"
  /\ LET v == captured
         p == v.proof
         usable == /\ p.epoch > 0
                   /\ p.policy = v.policy \/ Fault = "policy"
                   /\ MemberScope(p.members, v.live, v.scope)
                   /\ p.epoch = 1 \/ v.base2 \/ Fault = "generation"
         dep == IF Fault = "dependency" THEN {}
                ELSE BaseMembers(IF Fault = "generation" THEN 1 ELSE p.epoch)
         members == p.members \cup dep
         sent == IF Fault = "companion" THEN members \ {"C"} ELSE members
     IN /\ offered' = IF usable THEN sent ELSE {}
        /\ needed' = Roots(v.head)
        /\ residual' = IF usable THEN Roots(v.head) \ Roots(p.epoch) ELSE Roots(v.head)
        /\ scopedOffer' = (~usable \/ (p.policy = v.policy /\ MemberScope(sent, v.live, v.scope)))
        /\ oldTipOffer' = (usable /\ p.epoch < v.head)
  /\ crossed' = (rev # captured.rev)
  /\ fetch' = "done"
  /\ UNCHANGED <<live, scope, policy, head, rev, base2, retired, reclassified,
       phase, token, candidate, certificate, bindingOK, retried, captured, retryBind>>

WorkNext == Prepare \/ Bind \/ Retry \/ Retire \/ Reclassify \/ ChangePolicy
        \/ Push \/ BaseProof \/ Capture \/ Select
\* Make the stuttering already permitted by [][Next]_vars explicit to TLC.
\* This adds no behavior to Spec and does not assert progress or deadlock freedom.
Next == WorkNext \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
TypeOK ==
  /\ live \subseteq Packs /\ scope \in [Packs -> {"code", "meta"}]
  /\ policy \in 0..1 /\ head \in 1..2 /\ rev \in 0..6 /\ token \in 0..6
  /\ base2 \in BOOLEAN /\ retired \in BOOLEAN /\ reclassified \in BOOLEAN
  /\ phase \in {"prepare", "publish", "done"} /\ fetch \in {"idle", "select", "done"}
  /\ candidate \in [epoch : 0..2, policy : 0..1, members : SUBSET Packs]
  /\ certificate \in [epoch : 0..2, policy : 0..1, members : SUBSET Packs]
  /\ bindingOK \in BOOLEAN /\ retried \in BOOLEAN /\ scopedOffer \in BOOLEAN
  /\ offered \subseteq Packs /\ residual \subseteq {"a", "b", "c", "d"}
  /\ needed \subseteq {"a", "b", "c", "d"}
  /\ oldTipOffer \in BOOLEAN /\ retryBind \in BOOLEAN /\ crossed \in BOOLEAN
BindingSound == bindingOK
OfferScoped == scopedOffer
CompleteFetch == fetch = "done" => needed \subseteq Objects(offered) \cup residual
NoMetadata == "m" \notin Objects(offered)
NoRetryBind == ~retryBind
NoOldTipOffer == ~oldTipOffer
NoCompleteNewOffer == ~(fetch = "done" /\ captured.proof.epoch = 2 /\ offered # {})
NoConcurrentOffer == ~(fetch = "done" /\ crossed /\ offered # {})
=============================================================================
