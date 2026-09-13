---------------------------- MODULE WALContract ----------------------------
(***************************************************************************)
(* Intent-level correctness contract: git host whose only durable state   *)
(* is an object-store bucket, N ephemeral coordination-free instances,    *)
(* stock git clients.  One repository (repos are independent, Q7).        *)
(*                                                                         *)
(* Environment axioms modeled, not proven: per-object CAS (CommitPush /   *)
(* Fold atomicity on hist), immutable creation (objs monotone), no        *)
(* multi-object txns (single hist), no fencing (no lease guards anywhere),*)
(* crash-anywhere (stall + LoseAck + Crash), at-least-once (re-PushBegin),*)
(* no clocks (no timing anywhere).                                        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Refs,        \* ref names, e.g. {rA, rB}
  Vals,        \* abstract tips incl. None ("ref absent"), e.g. {None,v1,v2,v3}
  None,
  Objs,        \* abstract durable objects (the closure universe)
  Reach,       \* [Vals -> SUBSET Objs]: closure of each tip
  Clients,     \* symmetric
  Instances,   \* symmetric
  TxnPool,     \* abstract projections of complete, unfiltered submissions
  MaxPushes,   \* bound on push attempts (model bound, not a system limit)
  FoldBound    \* target unfolded-suffix length for T14

ASSUME /\ None \in Vals /\ Reach[None] = {}
       /\ \A v \in Vals : Reach[v] \subseteq Objs
       /\ \A t \in TxnPool :
            /\ t.refs \subseteq Refs /\ t.refs # {}
            /\ t.old \in [t.refs -> Vals] /\ t.new \in [t.refs -> Vals]
            /\ t.provides \subseteq Objs   \* objects the push carries

VARIABLES hist, acked, objs, live, pend, nextId, rd, obs, view
vars == <<hist, acked, objs, live, pend, nextId, rd, obs, view>>

(* ------------------------- derived state ------------------------------ *)
PushIdxs == { n \in 1..Len(hist) : hist[n].kind = "push" }

RefsAt(n) ==                       \* fold of the first n entries (refs only)
  LET F[m \in 0..n] ==
        IF m = 0 THEN [r \in Refs |-> None]
        ELSE IF hist[m].kind = "push"
             THEN [r \in Refs |-> IF r \in hist[m].txn.refs
                                  THEN hist[m].txn.new[r] ELSE F[m-1][r]]
             ELSE F[m-1]           \* folds change no refs: T8 by construction
  IN F[n]

Cur       == RefsAt(Len(hist))
Needed(n) == UNION { Reach[RefsAt(n)[r]] : r \in Refs }
NeedOf(t) == UNION { Reach[t.new[r]]     : r \in t.refs }

LastFold == IF \E n \in 1..Len(hist) : hist[n].kind = "fold"
            THEN CHOOSE n \in 1..Len(hist) :
                   /\ hist[n].kind = "fold"
                   /\ \A m \in (n+1)..Len(hist) : hist[m].kind # "fold"
            ELSE 0
Unfolded == Cardinality({ n \in PushIdxs : n > LastFold })

(* --------------------------- push lifecycle --------------------------- *)
\* There is deliberately no client "atomic" bit: each selected TxnPool record
\* is assumed to project one complete request and commits all-or-none. Ordering,
\* push options, derived metadata, parsing and reporting are erased. PushBegin
\* gives each attempt a fresh independent id; physical batches are not modeled.
PushBegin(c) ==                    \* stock git: client states old/new per ref
  /\ nextId <= MaxPushes
  /\ \E t \in TxnPool :
       pend' = [x \in DOMAIN pend \cup {nextId} |->
                  IF x = nextId THEN [txn |-> t, stage |-> "new"] ELSE pend[x]]
  /\ nextId' = nextId + 1
  /\ UNCHANGED <<hist, acked, objs, live, rd, obs, view>>

Upload(id) ==                      \* durable candidate creation; not committed state
  /\ id \in DOMAIN pend /\ pend[id].stage = "new"
  /\ objs' = objs \cup pend[id].txn.provides
  /\ live' = live \cup pend[id].txn.provides
  /\ pend' = [pend EXCEPT ![id].stage = "up"]
  /\ UNCHANGED <<hist, acked, nextId, rd, obs, view>>

CommitPush(id) ==                  \* THE linearization point: complete member
  /\ id \in DOMAIN pend /\ pend[id].stage = "up"
  /\ \A r \in pend[id].txn.refs :             \* per-ref old-value CAS   (T4)
       Cur[r] = pend[id].txn.old[r]
  /\ NeedOf(pend[id].txn) \subseteq live      \* closure durable at commit (T6)
  /\ hist' = Append(hist, [kind |-> "push", id |-> id, txn |-> pend[id].txn])
  /\ pend' = [pend EXCEPT ![id].stage = "cmt"]
  /\ UNCHANGED <<acked, objs, live, nextId, rd, obs, view>>

NackPush(id) ==                    \* truthful ng: mismatch is real (T11, Q4)
  /\ id \in DOMAIN pend /\ pend[id].stage \in {"new", "up"}
  /\ \E r \in pend[id].txn.refs : Cur[r] # pend[id].txn.old[r]
  /\ pend' = [pend EXCEPT ![id].stage = "ng"]
  /\ UNCHANGED <<hist, acked, objs, live, nextId, rd, obs, view>>

AckPush(id) ==                     \* ok strictly after commit (T1, A)
  /\ id \in DOMAIN pend /\ pend[id].stage = "cmt"
  /\ acked' = acked \cup {id}
  /\ pend' = [pend EXCEPT ![id].stage = "ack"]
  /\ UNCHANGED <<hist, objs, live, nextId, rd, obs, view>>

LoseAck(id) ==                     \* crash exit: committed, ok never delivered
  /\ id \in DOMAIN pend /\ pend[id].stage = "cmt"
  /\ pend' = [x \in DOMAIN pend \ {id} |-> pend[x]]
  /\ UNCHANGED <<hist, acked, objs, live, nextId, rd, obs, view>>

(* --------------------------- maintenance ------------------------------ *)
Fold ==                            \* any instance, no lease; neutral (T8, T10)
  /\ Unfolded > 0
  /\ hist' = Append(hist, [kind |-> "fold", upto |-> Len(hist)])
  /\ UNCHANGED <<acked, objs, live, pend, nextId, rd, obs, view>>

Trim(S) ==                         \* OPTIONAL (non-property #13, Q2); guarded:
  /\ S \subseteq live /\ S # {}
  /\ S \cap Needed(Len(hist)) = {}                       \* current closure (T6)
  /\ \A c \in Clients : rd[c].act =>                       \* active reads (Q3)
       S \cap (UNION { Needed(j) : j \in rd[c].lo..Len(hist) }) = {}
  /\ \A id \in DOMAIN pend : pend[id].stage = "up" =>      \* pending push (Q10)
       S \cap NeedOf(pend[id].txn) = {}
  /\ live' = live \ S
  /\ UNCHANGED <<hist, acked, objs, pend, nextId, rd, obs, view>>

(* ------------------------------ reads --------------------------------- *)
ReadBegin(c) ==
  /\ ~rd[c].act
  /\ rd' = [rd EXCEPT ![c] = [act |-> TRUE, lo |-> Len(hist)]]
  /\ UNCHANGED <<hist, acked, objs, live, pend, nextId, obs, view>>

\* Any instance may serve, warm or cold; there is no view[i] guard (T9/T10).
ReadEnd(c, i) ==
  /\ rd[c].act     \* Linearizes at some instant within the window (T2, T3):
  /\ \E j \in rd[c].lo..Len(hist) :   \* served bytes := RefsAt(j) + its closure
       /\ obs'  = [obs  EXCEPT ![c] = j]
       /\ view' = [view EXCEPT ![i] = IF j > view[i] THEN j ELSE view[i]]
  /\ rd' = [rd EXCEPT ![c] = [act |-> FALSE, lo |-> 0]]
  /\ UNCHANGED <<hist, acked, objs, live, pend, nextId>>

(* --------------------------- failure model ---------------------------- *)
Crash(i) ==        \* instance loses ALL local state; also models cold start.
  /\ view' = [view EXCEPT ![i] = 0]    \* warmth only (T1/T9)
  /\ UNCHANGED <<hist, acked, objs, live, pend, nextId, rd, obs>>
  \* In-flight pushes stalling forever ≈ their instance crashed (no fairness
  \* is attached to any single op unless we assert T12).

(* ------------------------------ spec ---------------------------------- *)
Init == /\ hist = <<>> /\ acked = {} /\ objs = {} /\ live = {}
        /\ pend = [x \in {} |-> x] /\ nextId = 1
        /\ rd  = [c \in Clients |-> [act |-> FALSE, lo |-> 0]]
        /\ obs = [c \in Clients |-> 0]
        /\ view = [i \in Instances |-> 0]

Next == \/ \E c \in Clients : PushBegin(c) \/ ReadBegin(c)
        \/ \E c \in Clients, i \in Instances : ReadEnd(c, i)
        \/ \E id \in DOMAIN pend :
             Upload(id) \/ CommitPush(id) \/ NackPush(id)
                        \/ AckPush(id)    \/ LoseAck(id)
        \/ Fold
        \/ \E S \in SUBSET Objs : Trim(S)
        \/ \E i \in Instances : Crash(i)

Fairness ==        \* needed ONLY by T12/T13/T14; safety holds without any.
  /\ \A id \in 1..MaxPushes :
       /\ WF_vars(Upload(id)) /\ WF_vars(AckPush(id))
       /\ SF_vars(CommitPush(id) \/ NackPush(id))
          \* SF encodes "contention eventually resolves" — stronger than the
          \* design promises (Q5); with WF only, alternating CAS losers is a
          \* legal run and T12's success clause fails. Deliberate and flagged.
  /\ \A c \in Clients, i \in Instances : WF_vars(ReadEnd(c, i))
  /\ WF_vars(Fold)
  \* NO fairness on Crash, Trim, PushBegin: they may happen anytime or never.

Spec == Init /\ [][Next]_vars /\ Fairness

(* ========================= THE CONTRACT ================================ *)

(* Contract mapping (docs/spec/README.md §2):                               *)
(*   C1=AckedCommitted   C2=ReadFresh   C3=Mono   C4=HistPreconds          *)
(*   C6a=ClosureLive   C8=AckAfterCommit                                  *)
(*   C10b=Trim's guard   C15=PushTerminates+ReadsTerminate                 *)
(*   C16=EventuallyFolded   C10a/C11/C12 = by construction (README §7)     *)
(* C5b's ref-state core is structural under the whole-request assumption.    *)
(* Policy/reporting/batching are refinement obligations. Raw candidate-byte   *)
(* serving is not modeled: Upload adds closure-check availability only.       *)

(* ---- state invariants (SAFETY) ---- *)
TypeOK ==
  /\ acked \subseteq 1..MaxPushes /\ live \subseteq objs /\ objs \subseteq Objs
  /\ \A n \in 1..Len(hist) : hist[n].kind \in {"push", "fold"}
  /\ \A c \in Clients : obs[c] \in 0..Len(hist) /\ rd[c].lo \in 0..Len(hist)

AckedCommitted ==   \* T1 (with objs durability via ClosureLive + Mono)
  \A id \in acked : \E n \in PushIdxs : hist[n].id = id

\* T4: every committed txn's old values matched its prior state.
HistPreconds ==
  \A n \in PushIdxs : \A r \in hist[n].txn.refs :
     RefsAt(n-1)[r] = hist[n].txn.old[r]

ClosureLive ==      \* T6: the published state is self-contained, always
  Needed(Len(hist)) \subseteq live

NoPhantomPush ==    \* T7: every committed txn traces to a client request
  \A n \in PushIdxs : hist[n].id < nextId

(* T15, OPTIONAL — check only with Trim disabled, or windowed per Q2: *)
ProvenanceAll == \A n \in 0..Len(hist) : Needed(n) \subseteq live

(* ---- action properties ([][...]_vars) ---- *)
Mono ==             \* T3 (append-only, no rollback) + monotone acks/objs +
  [][ /\ acked \subseteq acked' /\ objs \subseteq objs'   \* monotone sessions
      /\ Len(hist') >= Len(hist)
      /\ \A n \in 1..Len(hist) : hist'[n] = hist[n]
      /\ \A c \in Clients : obs'[c] >= obs[c] ]_vars

\* T2: a read never returns anything older than its window floor.
ReadFresh ==
  [][ \A c \in Clients :
        (rd[c].act /\ ~rd'[c].act) => obs'[c] >= rd[c].lo ]_vars
  \* T2 end-to-end: at ReadBegin, lo = Len(hist) >= index of every already-acked
  \* push (AckedCommitted + Mono), so the served j >= lo covers them all.

AckAfterCommit ==   \* T1/T11: ok never precedes commit
  [][ \A id \in 1..MaxPushes :
        (id \in acked' /\ id \notin acked) =>
           \E n \in PushIdxs : hist[n].id = id ]_vars

(* ---- temporal properties (LIVENESS; require Fairness) ---- *)
PushTerminates ==   \* T12 (LoseAck counts: visible connection failure)
  \A id \in 1..MaxPushes :
    (id \in DOMAIN pend) ~>
       (id \notin DOMAIN pend \/ pend[id].stage \in {"ack", "ng"})

ReadsTerminate ==   \* T13
  \A c \in Clients : rd[c].act ~> ~rd[c].act

EventuallyFolded == \* T14 (meaningful because PushBegin is bounded: quiescence)
  <>[](Unfolded <= FoldBound)

(* C5b/T5's ref-state projection, T8 (fold neutrality), and T9 (cold-start
   fidelity) are BY CONSTRUCTION here: the model assumes one complete request
   per txn and uses one hist entry per push; fold entries skip refs in RefsAt,
   and no property mentions view. Parsing, ordering, policy, reports, broker
   forwarding, and physical group batching remain refinement obligations.
   For the abstract spec these properties are
   structural; for implementations they are refinement obligations (§4d),
   which is exactly where the design places the burden.                     *)
=============================================================================
