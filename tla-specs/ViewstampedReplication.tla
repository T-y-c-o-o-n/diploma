----------------------- MODULE ViewstampedReplication -----------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

Status == {Normal, ViewChange, Recovering}

\* Client operation
CONSTANT Operation

\* Result of executing operation
Result == Operation

RequestNumber == Nat

\* Special value
CONSTANT None

\* Message types for processing client request
CONSTANTS Request, Prepare, PrepareOk, Reply, Commit

\* Message types for view changing
CONSTANTS StartViewChange, DoViewChange, StartView

\* Message types for replica recovery
CONSTANTS Recovery, RecoveryResponse

\* Sequence with all replicas (for view selection)
CONSTANT ReplicaSequence

\* State on each replica
VARIABLES viewNumber, status, lastNormalView,
          opNumber, log, commitNumber, prepared,
          executedOperations

\* State on Primary replica
VARIABLES sentPreparedOpNumber, recievedPrepareOkOpNumber, sentCommitNumber, sentStartView

\* State on View Changing replica
VARIABLES sentStartViewChange, recievedStartViewChange, recievedDoViewChangeMsgs

VARIABLE msgs

replicaViewVars == <<viewNumber, status, lastNormalView>>

replicaViewChangeVars == <<sentStartViewChange, recievedStartViewChange, recievedDoViewChangeMsgs>>

replicaLogVars == <<opNumber, log>>

replicaExecVars == <<commitNumber, prepared, executedOperations>>

primaryVars == <<sentPreparedOpNumber, recievedPrepareOkOpNumber, sentCommitNumber, sentStartView>>

replicaStateVars == <<replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars>>

vars == <<replicaStateVars, msgs>>

-----------------------------------------------------------------------------

View == Nat

OpNumber == Nat

CommitNumber == Nat

RequestMessage == [type: {Request}, op: Operation]

LogEntry == [opNumber: Nat, m: RequestMessage]

\* All possible messages
Message == [src: Replica, dst: Replica, type: {Prepare}, v: View, m: RequestMessage, n: OpNumber, k: CommitNumber]
      \cup [src: Replica, dst: Replica, type: {PrepareOk}, v: View, n: OpNumber, i: Replica]
      \cup [src: Replica, dst: Replica, type: {Commit}, v: View, k: CommitNumber]
      \cup [src: Replica, dst: Replica, type: {StartViewChange}, v: View, i: Replica]
      \cup [src: Replica, dst: Replica, type: {DoViewChange}, v: View, l: Seq(LogEntry), vv: View, n: OpNumber, k: CommitNumber, i: Replica]
      \cup [src: Replica, dst: Replica, type: {StartView}, v: View, l: Seq(LogEntry), n: OpNumber, k: CommitNumber]

\* TODO: add losing, dublicating, out of order messages
Send(m) == msgs' = msgs \cup {m}

Drop(m) == 
    /\ msgs' = msgs \ {m}

ReplyMessage(request, response) ==
    /\ request \in msgs
    /\ msgs' = (msgs \ {request}) \cup {response}

TypeOK == /\ viewNumber \in [Replica -> View]
          /\ status \in [Replica -> Status]
          /\ lastNormalView \in [Replica -> View]
          /\ sentStartViewChange \in [Replica -> SUBSET Replica]
          /\ recievedStartViewChange \in [Replica -> SUBSET Replica]
          /\ recievedDoViewChangeMsgs \in [Replica -> SUBSET Message]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ commitNumber \in [Replica -> Nat]
          /\ prepared \in [Replica -> Nat]
          /\ executedOperations \in [Replica -> Seq(RequestMessage)]
          /\ sentPreparedOpNumber \in [Replica -> [Replica -> OpNumber]]
          /\ recievedPrepareOkOpNumber \in [Replica -> [Replica -> OpNumber]]
          /\ sentCommitNumber \in [Replica -> [Replica -> CommitNumber]]
          /\ sentStartView \in [Replica -> SUBSET Replica]
          /\ msgs \in SUBSET Message

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

ASSUME IsFiniteSet(Replica)

max(S) == CHOOSE x \in S: \A y \in S: y <= x

lastOpNumber(l) == IF l = <<>> THEN 0 ELSE l[Len(l)].opNumber

-----------------------------------------------------------------------------

Init == /\ viewNumber = [r \in Replica |-> 0]
        /\ status = [r \in Replica |-> Normal]
        /\ lastNormalView = [r \in Replica |-> 0]
        /\ sentStartViewChange = [r \in Replica |-> {}]
        /\ recievedStartViewChange = [r \in Replica |-> {}]
        /\ recievedDoViewChangeMsgs = [r \in Replica |-> {}]
        /\ opNumber = [r \in Replica |-> 0]
        /\ log = [r \in Replica |-> << >>]
        /\ commitNumber = [r \in Replica |-> 0]
        /\ prepared = [r \in Replica |-> 0]
        /\ executedOperations = [r \in Replica |-> << >>]
        /\ sentPreparedOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
        /\ recievedPrepareOkOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
        /\ sentCommitNumber = [p \in Replica |-> [r \in Replica |-> 0]]
        /\ sentStartView = [r \in Replica |-> {}]
        /\ msgs = {}

-----------------------------------------------------------------------------

\* Think how to implement it
GenerateOperation == CHOOSE op \in Operation: TRUE

ExecuteOperation(op) == op

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, viewNumber[r])

AddClientRequest(r, m) ==
    /\ opNumber' = [opNumber EXCEPT ![r] = opNumber[r] + 1]
    /\ log' = [log EXCEPT ![r] = Append(log[r], [opNumber |-> opNumber'[r], m |-> m])]

\* Implemented as Primary "generates" it by itself
RecieveClientRequest(p) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ AddClientRequest(p, [type |-> Request, op |-> GenerateOperation])
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaExecVars, primaryVars, msgs>>

SendPrepare(p, r) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ p # r
    /\ sentPreparedOpNumber[p][r] < Len(log[p])
    /\ LET sentOpNumber == sentPreparedOpNumber[p][r] + 1
       IN /\ sentPreparedOpNumber' = [sentPreparedOpNumber EXCEPT ![p][r] = sentOpNumber]
          /\ Send([src |-> p, dst |-> r, type |-> Prepare,
                   v |-> viewNumber[p], m |-> log[p][sentOpNumber].m,
                   n |-> sentOpNumber, k |-> commitNumber[p]])
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, sentStartView, recievedPrepareOkOpNumber, sentCommitNumber>>

RecievePrepare(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ status[r] = Normal
    /\ m.type = Prepare
    /\ m.n = opNumber[r] + 1
    /\ AddClientRequest(r, m.m)
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaExecVars, primaryVars, msgs>>

PrepareOperation(r) ==
    /\ ~IsPrimary(r)
    /\ status[r] = Normal
    /\ prepared[r] < Len(log[r])
    /\ prepared' = [prepared EXCEPT ![r] = prepared[r] + 1]
    /\ Send([src |-> r, dst |-> PrimaryReplicaInView(viewNumber[r]), type |-> PrepareOk,
             v |-> viewNumber[r], n |-> log[r][prepared'[r]].opNumber, i |-> r])
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, commitNumber, executedOperations, primaryVars>>

ExecuteRequest(r, request) ==
    /\ executedOperations' = [executedOperations EXCEPT ![r] = Append(executedOperations[r], request)]

ExecuteClientRequest(r) ==
    /\ status[r] = Normal
    /\ Len(executedOperations[r]) < commitNumber[r]
    /\ Len(log[r]) >= Len(executedOperations[r]) + 1
    /\ ExecuteRequest(r, log[r][Len(executedOperations[r]) + 1].m)
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, commitNumber, prepared, primaryVars, msgs>>

CheckAchievePrepareOkFromQuorum(p) ==
    /\ LET newCommit == commitNumber[p] + 1
       IN IF \E Q \in Quorum:
                 \A r \in Q:
                     \/ recievedPrepareOkOpNumber[p][r] >= newCommit
                     \/ r = p
          THEN /\ commitNumber' = [commitNumber EXCEPT ![p] = newCommit]
               /\ ExecuteRequest(p, log[p][newCommit].m)
               /\ UNCHANGED <<prepared>>
          ELSE UNCHANGED <<replicaExecVars>>

RecievePrepareOk(p, m) ==
    /\ m.type = PrepareOk
    /\ p # m.i
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ \/ \* stale prepareOkMessage
          /\ m.n <= recievedPrepareOkOpNumber[p][m.i]
          /\ UNCHANGED <<recievedPrepareOkOpNumber>>
       \/ \* 
          /\ m.n > recievedPrepareOkOpNumber[p][m.i]
          /\ recievedPrepareOkOpNumber' = [recievedPrepareOkOpNumber EXCEPT ![p][m.i] = m.n]
    /\ CheckAchievePrepareOkFromQuorum(p)
    /\ Drop(m)
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, sentPreparedOpNumber, sentCommitNumber, sentStartView>>

SendCommit(p, r) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ p # r
    /\ sentCommitNumber[p][r] < commitNumber[p]
    /\ Send([src |-> p, dst |-> r, type |-> Commit,
             v |-> viewNumber[p], k |-> commitNumber[p]])
    /\ sentCommitNumber' = [sentCommitNumber EXCEPT ![p][r] = commitNumber[p]]
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, sentPreparedOpNumber, recievedPrepareOkOpNumber, sentStartView>>

RecieveCommit(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ status[r] = Normal
    /\ m.type = Commit
    /\ m.k > commitNumber[r]
    /\ commitNumber' = [commitNumber EXCEPT ![r] = m.k]
    /\ Drop(m)  \* TODO: don't remove or send to every replica different messages
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, prepared, executedOperations, primaryVars>>

-----------------------------------------------------------------------------

(* View Changing *)

TimeoutStartViewChanging(r) ==
    /\ status[r] = Normal
    /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[r] + 1]
    /\ status' = [status EXCEPT ![r] = ViewChange]
    /\ UNCHANGED <<lastNormalView, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars, msgs>>

SendStartViewChange(r1, r2) ==
    /\ status[r1] = ViewChange
    /\ r1 # r2
    /\ ~ (r2 \in sentStartViewChange[r1])
    /\ Send([src |-> r1, dst |-> r2, type |-> StartViewChange, v |-> viewNumber[r1], i |-> r1])
    /\ sentStartViewChange' = [sentStartViewChange EXCEPT ![r1] = sentStartViewChange[r1] \cup {r2}]
    /\ UNCHANGED <<replicaViewVars, recievedStartViewChange, recievedDoViewChangeMsgs, replicaLogVars, replicaExecVars, primaryVars>>

CheckAchieveStartViewChangeFromQuorum(r, m) ==
    /\ IF \E Q \in Quorum: /\ r \in Q
                           /\ Q = recievedStartViewChange'[r] \cup {r}
       THEN ReplyMessage(
               m,
               [src |-> r, dst |-> PrimaryReplicaInView(m.v),
                type |-> DoViewChange, v |-> m.v,
                l |-> log[r], vv |-> lastNormalView[r],
                n |-> opNumber[r], k |-> commitNumber[r], i |-> r])
       ELSE Drop(m)

RecieveStartViewChange(r, m) ==
    /\ m.type = StartViewChange
    /\ \/ \* Start View Changing
          /\ m.v > viewNumber[r]
          /\ viewNumber' = [viewNumber EXCEPT ![r] = m.v]
          /\ status' = [status EXCEPT ![r] = ViewChange]
          /\ sentStartViewChange' = [sentStartViewChange EXCEPT ![r] = {}]
          /\ recievedStartViewChange' = [recievedStartViewChange EXCEPT ![r] = {m.i}]
          /\ CheckAchieveStartViewChangeFromQuorum(r, m)
          /\ UNCHANGED <<lastNormalView, recievedDoViewChangeMsgs>>
       \/ \* Our view number
          /\ m.v = viewNumber[r]
          /\ status[r] = ViewChange
          /\ recievedStartViewChange' = [recievedStartViewChange EXCEPT ![r] = recievedStartViewChange[r] \cup {m.i}]
          /\ CheckAchieveStartViewChangeFromQuorum(r, m)
          /\ UNCHANGED <<replicaViewVars, sentStartViewChange, recievedDoViewChangeMsgs>>
       \/ \* Stale view
          /\ \/ m.v < viewNumber[r]
             \/ /\ m.v = viewNumber[r]
                /\ status[r] = Normal
          /\ Drop(m)
          /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars>>
    /\ UNCHANGED <<replicaLogVars, replicaExecVars, primaryVars>>

RecieveDoViewChange(p, m) ==
    /\ m.type = DoViewChange
    /\ IsPrimaryInView(p, m.v)
    /\ \/ \* Update view number
          /\ m.v > viewNumber[p]
          /\ viewNumber' = [viewNumber EXCEPT ![p] = m.v]
          /\ status' = [status EXCEPT ![p] = ViewChange]
          /\ recievedDoViewChangeMsgs' = [recievedDoViewChangeMsgs EXCEPT ![p] = {m}]
          /\ UNCHANGED <<lastNormalView, sentStartViewChange, recievedStartViewChange>>
       \/ \* Our view number
          /\ m.v = viewNumber[p]
          /\ status[p] = ViewChange
          /\ recievedDoViewChangeMsgs' = [recievedDoViewChangeMsgs EXCEPT ![p] = recievedDoViewChangeMsgs[p] \cup {m}]
          /\ UNCHANGED <<replicaViewVars, sentStartViewChange, recievedStartViewChange>>
       \/ \* Stale message
          /\ m.v < viewNumber[p]
          /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars>>
    /\ Drop(m)
    /\ UNCHANGED <<replicaLogVars, replicaExecVars, primaryVars>>

\* Become Primary
AchieveDoViewChangeFromQuorum(p) ==
    /\ status[p] = ViewChange
    /\ \E Q \in Quorum: /\ p \in Q
                        /\ Q \subseteq {m.i : m \in recievedDoViewChangeMsgs[p]}
    /\ LET maxVV == max({m.vv : m \in recievedDoViewChangeMsgs[p]})
           maxN == max({m.n : m \in {m \in recievedDoViewChangeMsgs[p] : m.vv = maxVV}})
           maxMsg == CHOOSE m \in recievedDoViewChangeMsgs[p]: m.vv = maxVV /\ m.n = maxN
           newLog == maxMsg.l
       IN /\ log' = [log EXCEPT ![p] = newLog]
          /\ opNumber' = [opNumber EXCEPT ![p] = lastOpNumber(newLog)]
    /\ commitNumber' = [commitNumber EXCEPT ![p] = max({m.k : m \in recievedDoViewChangeMsgs[p]})]
    /\ status' = [status EXCEPT ![p] = Normal]
    /\ lastNormalView' = [lastNormalView EXCEPT ![p] = viewNumber[p]]
    /\ sentStartView' = [sentStartView EXCEPT ![p] = {}]
    /\ sentStartViewChange' = [sentStartViewChange EXCEPT ![p] = {}]
    /\ recievedStartViewChange' = [recievedStartViewChange EXCEPT ![p] = {}]
    /\ recievedDoViewChangeMsgs' = [recievedDoViewChangeMsgs EXCEPT ![p] = {}]
    /\ UNCHANGED <<viewNumber, prepared, executedOperations, sentPreparedOpNumber, recievedPrepareOkOpNumber, sentCommitNumber, msgs>>

SendStartView(p, r) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ p # r
    /\ ~ (r \in sentStartView[p])
    /\ Send([src |-> p, dst |-> r, type |-> StartView,
             v |-> viewNumber[p], l |-> log[p], n |-> opNumber[p], k |-> commitNumber[p]])
    /\ sentStartView' = [sentStartView EXCEPT ![p] = sentStartView[p] \cup {r}]
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, sentPreparedOpNumber, recievedPrepareOkOpNumber, sentCommitNumber>>

RecieveStartView(r, m) ==
    /\ m.type = StartView
    /\ \/ m.v > viewNumber[r]
       \/ /\ m.v = viewNumber[r]
          /\ status = ViewChange
    /\ log' = [log EXCEPT ![r] = m.l]
    /\ opNumber' = [opNumber EXCEPT ![r] = m.n]
    /\ viewNumber' = [viewNumber EXCEPT ![r] = m.v]
    /\ status' = [status EXCEPT ![r] = Normal]
    /\ lastNormalView' = [lastNormalView EXCEPT ![r] = viewNumber[r]]
    /\ commitNumber' = [commitNumber EXCEPT ![r] = m.k]
    /\ prepared' = [prepared EXCEPT ![r] = m.k]
    /\ UNCHANGED <<replicaViewChangeVars, executedOperations, primaryVars, msgs>>

-----------------------------------------------------------------------------



Next == \/ \E r \in Replica: RecieveClientRequest(r)
        \/ \E p, r \in Replica: SendPrepare(p, r)
        \/ \E r \in Replica, m \in msgs: RecievePrepare(r, m) /\ m.dst = r
        \/ \E r \in Replica: PrepareOperation(r)
        \/ \E r \in Replica, m \in msgs: RecievePrepareOk(r, m) /\ m.dst = r
        \/ \E r \in Replica, m \in msgs: RecieveCommit(r, m) /\ m.dst = r
        \/ \E r \in Replica: ExecuteClientRequest(r)
        \/ \E p, r \in Replica: SendCommit(p, r)
        \/ \E r \in Replica: TimeoutStartViewChanging(r)
        \/ \E p, r \in Replica: SendStartViewChange(p, r)
        \/ \E r \in Replica, m \in msgs: RecieveStartViewChange(r, m) /\ m.dst = r
        \/ \E p \in Replica, m \in msgs: RecieveDoViewChange(p, m)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
        \/ \E p, r \in Replica: SendStartView(p, r)
        \/ \E r \in Replica, m \in msgs: RecieveStartView(r, m) /\ m.dst = r

-----------------------------------------------------------------------------

(* Liveness *)

EventuallyRecieveClientRequest == \A r \in Replica: WF_vars(\E m \in msgs: RecieveClientRequest(r))

EventuallyRecievePrepare == \A r \in Replica: WF_vars(\E m \in msgs: RecievePrepare(r, m))

EventuallyRecieveCommit == \A r \in Replica: WF_vars(\E m \in msgs: RecieveCommit(r, m))

EventuallyRecievePrepareOk == \A p \in Replica: WF_vars(\E m \in msgs: RecievePrepareOk(p, m))

LivenessSpec ==
    /\ EventuallyRecieveClientRequest
    /\ EventuallyRecievePrepare
    /\ EventuallyRecieveCommit
    /\ EventuallyRecievePrepareOk

-----------------------------------------------------------------------------

(* Full Spec *)

Spec == Init /\ [][Next]_vars \* /\ LivenessSpec

-----------------------------------------------------------------------------

(* INVARIANTS *)

EveryViewHasAtLeastOnePrimary == \A v \in 0..10: \E r \in Replica: IsPrimaryInView(r, v)

EveryViewHasAtMostOnePrimary == \A v \in 0..10: \A r1, r2 \in Replica:
                                                    (IsPrimaryInView(r1, v) /\ IsPrimaryInView(r2, v)) => r1 = r2

PreficiesAreEqual(s1, s2) == \A i \in DOMAIN s1 \cap DOMAIN s2: s1[i] = s2[i]

ExecutedOperationsPreficesAreEqual == \A r1, r2 \in Replica: PreficiesAreEqual(executedOperations[r1], executedOperations[r2])

PreficiesOfLenAreEqual(s1, s2, prefLen) == \A i \in DOMAIN s1 \cap DOMAIN s2 \cap 1..prefLen: s1[i] = s2[i]

CommitedLogsPreficesAreEqual == \A r1, r2 \in Replica: PreficiesOfLenAreEqual(log[r1], log[r2], IF commitNumber[r1] <= commitNumber[r2] THEN commitNumber[r1] ELSE commitNumber[r2])

-----------------------------------------------------------------------------

(* Properties *)

\*AllClientsWillBeServed == \A c \in Client: (pendingRequest[c] ~> ~pendingRequest[c])



-----------------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Wed Nov 30 19:45:14 MSK 2022 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
