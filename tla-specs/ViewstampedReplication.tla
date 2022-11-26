----------------------- MODULE ViewstampedReplication -----------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Client, Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

Status == {Normal, ViewChange, Recovering}

\* Client operation
CONSTANT Operation

\* Result of executing operation
Result == Operation

ClientId == Nat

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
VARIABLES sentPreparedOpNumber, recievedPrepareOkOpNumber

\* State on View Changing replica
VARIABLES sentStartViewChange, sentStartView, recievedStartViewChange, recievedDoViewChangeMsgs

\* Clients state
VARIABLES lastRequestId, pendingRequest

VARIABLE msgs

replicaViewVars == <<viewNumber, status, lastNormalView>>

replicaViewChangeVars == <<sentStartViewChange, recievedStartViewChange, recievedDoViewChangeMsgs>>

replicaLogVars == <<opNumber, log>>

replicaExecVars == <<commitNumber, prepared, executedOperations>>

primaryVars == <<sentPreparedOpNumber, sentStartView, recievedPrepareOkOpNumber>>

replicaStateVars == <<replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars>>

clientStateVars == <<lastRequestId, pendingRequest>>

vars == <<clientStateVars, replicaStateVars, msgs>>

-----------------------------------------------------------------------------

View == Nat

OpNumber == Nat

CommitNumber == Nat

RequestMessage == [type: {Request}, op: Operation, c: Client, s: RequestNumber]

LogEntry == [opNumber: Nat, m: RequestMessage]

\* All possible messages
Message ==      RequestMessage
           \cup [src: Replica, dst: Replica, type: {Prepare}, v: View, m: RequestMessage, n: OpNumber, k: CommitNumber]
           \cup [src: Replica, dst: Replica, type: {PrepareOk}, v: View, n: OpNumber, i: Replica]
           \cup [type: {Reply}, v: View, s: RequestNumber, x: Result, c: Client]
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

TypeOK == /\ lastRequestId \in [Client -> Nat]
          /\ pendingRequest \in [Client -> BOOLEAN]
          /\ viewNumber \in [Replica -> View]
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
          /\ sentStartView \in [Replica -> SUBSET Replica]
          /\ sentPreparedOpNumber \in [Replica -> [Replica -> OpNumber]]
          /\ recievedPrepareOkOpNumber \in [Replica -> [Replica -> OpNumber]]
          /\ msgs \in SUBSET Message

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

ASSUME IsFiniteSet(Replica)

max(S) == CHOOSE x \in S: \A y \in S: y <= x

lastOpNumber(l) == IF l = <<>> THEN 0 ELSE l[Len(l)].opNumber

-----------------------------------------------------------------------------

Init == /\ lastRequestId = [c \in Client |-> 0]
        /\ pendingRequest = [c \in Client |-> FALSE]
        /\ viewNumber = [r \in Replica |-> 0]
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
        /\ sentStartView = [r \in Replica |-> {}]
        /\ sentPreparedOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
        /\ recievedPrepareOkOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
        /\ msgs = {}

-----------------------------------------------------------------------------

\* Think how to implement it
GenerateOperation == CHOOSE op \in Operation: TRUE

ExecuteOperation(op) == op

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, viewNumber[r])

ClientSendRequest(c) ==
    /\ ~pendingRequest[c]
    /\ lastRequestId' = [lastRequestId EXCEPT ![c] = lastRequestId[c] + 1]
    /\ pendingRequest' = [pendingRequest EXCEPT ![c] = TRUE]
    /\ Send([
        type |-> Request, op |-> GenerateOperation,
        c |-> c, s |-> lastRequestId'[c]])
    /\ UNCHANGED <<replicaStateVars>>

RecieveReply(c, m) ==
    /\ pendingRequest[c]
    /\ m.type = Reply
    /\ m.c = c
    /\ m.s = lastRequestId[c]
    /\ pendingRequest' = [pendingRequest EXCEPT ![c] = FALSE]
    /\ Drop(m)
    /\ UNCHANGED <<lastRequestId, replicaStateVars>>

AddClientRequest(r, m) ==
    /\ opNumber' = [opNumber EXCEPT ![r] = opNumber[r] + 1]
    /\ log' = [log EXCEPT ![r] = Append(log[r], [opNumber |-> opNumber'[r], m |-> m])]

RecieveClientRequest(r, m) ==
    /\ IsPrimary(r)
    /\ m.type = Request
    /\ AddClientRequest(r, m)
    /\ Drop(m)
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaViewChangeVars, replicaExecVars, primaryVars>>

SendPrepare(p, r) ==
    /\ IsPrimary(p)
    /\ p # r
    /\ sentPreparedOpNumber[p][r] < Len(log[p])
    /\ LET sentOpNumber == sentPreparedOpNumber[p][r] + 1
       IN /\ sentPreparedOpNumber' = [sentPreparedOpNumber EXCEPT ![p][r] = sentOpNumber]
          /\ Send([type |-> Prepare, v |-> viewNumber[p], m |-> log[sentOpNumber].m,
             n |-> sentOpNumber, k |-> commitNumber[p]])
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, recievedPrepareOkOpNumber>>

RecievePrepare(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.type = Prepare
    /\ m.n = opNumber[r] + 1
    /\ AddClientRequest(r, m.m)
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaViewChangeVars, commitNumber, prepared, executedOperations, primaryVars>>

PrepareOperation(r) ==
    /\ ~IsPrimary(r)
    /\ prepared[r] < Len(log[r])
    /\ prepared' = [prepared EXCEPT ![r] = prepared[r] + 1]
    /\ Send([src |-> r, dst |-> PrimaryReplicaInView(viewNumber[r]), type |-> PrepareOk,
             v |-> viewNumber[r], n |-> log[prepared'[r]].opNumber, i |-> r])
    /\ UNCHANGED <<>>

RecievePrepareOk(p, m) ==
    /\ m.type = PrepareOk
    /\ p # m.i
    /\ IsPrimary(p)
    /\ \/ \* stale prepareOkMessage
          /\ m.n <= recievedPrepareOkOpNumber[p][m.i]
          /\ UNCHANGED <<recievedPrepareOkOpNumber>>
       \/ \* 
          /\ m.n > recievedPrepareOkOpNumber[p][m.i]
          /\ recievedPrepareOkOpNumber' = [recievedPrepareOkOpNumber EXCEPT ![p][m.i] = m.n]
    /\ Drop(m)
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaViewChangeVars, opNumber, log, commitNumber, prepared, executedOperations>>

ExecuteRequest(r, request) ==
    /\ executedOperations' = [executedOperations EXCEPT ![r] = Append(executedOperations[r], request)]

ExecuteClientRequest(r) ==
    /\ Len(executedOperations[r]) < commitNumber[r]
    /\ Len(log[r]) >= Len(executedOperations[r]) + 1
    /\ ExecuteRequest(r, log[r][Len(executedOperations[r]) + 1].m)
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaViewChangeVars, opNumber, log, commitNumber, prepared, primaryVars, msgs>>

AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ LET newCommit == commitNumber[p] + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ recievedPrepareOkOpNumber[p][r] >= newCommit
                     \/ r = p
          /\ commitNumber' = [commitNumber EXCEPT ![p] = newCommit]
          /\ ExecuteRequest(p, log[p][newCommit].m)
          /\ Send([type |-> Reply, v |-> viewNumber[p],
                   s |-> log[p][newCommit].m.s,
                   x |-> ExecuteOperation(log[p][newCommit].op),
                   c |-> log[p][commitNumber'[p]].m.c])
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaViewChangeVars, opNumber, log, prepared, primaryVars>>

SendCommit(p, r) ==
    /\ IsPrimary(p)
    /\ p # r
    /\ Send([src |-> p, dst |-> r, type |-> Commit,
             v |-> viewNumber[p], k |-> commitNumber[p]])
    /\ UNCHANGED <<clientStateVars, replicaStateVars>>

RecieveCommit(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.type = Commit
    /\ m.k > commitNumber[r]
    /\ commitNumber' = [commitNumber EXCEPT ![r] = m.k]
    /\ Drop(m)  \* TODO: don't remove or send to every replica different messages
    /\ UNCHANGED <<clientStateVars, viewNumber, status, lastNormalView, replicaViewChangeVars, recievedStartViewChange, recievedDoViewChangeMsgs, opNumber, log, prepared, executedOperations, primaryVars>>

-----------------------------------------------------------------------------

(* View Changing *)

TimeoutStartViewChanging(r) ==
    /\ status[r] = Normal
    /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[r] + 1]
    /\ status' = [status EXCEPT ![r] = ViewChange]
    /\ UNCHANGED <<clientStateVars, lastNormalView, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars, msgs>>

SendStartViewChange(p, r) ==
    /\ status[r] = ViewChange
    /\ p # r
    /\ ~ (r \in sentStartViewChange[p])
    /\ Send([src |-> p, dst |-> r, type |-> StartViewChange, v |-> viewNumber[p], i |-> p])
    /\ sentStartViewChange' = [sentStartViewChange EXCEPT ![p] = sentStartViewChange[p] \cup {r}]
    /\ UNCHANGED <<clientStateVars, replicaViewVars, recievedStartViewChange, recievedDoViewChangeMsgs, replicaLogVars, replicaExecVars, primaryVars>>

RecieveStartViewChange(r, m) ==
    /\ m.type = StartViewChange
    /\ \/ \* Start View Changing
          /\ m.v > viewNumber[r]
          /\ viewNumber' = [viewNumber EXCEPT ![r] = m.v]
          /\ status' = [status EXCEPT ![r] = ViewChange]
          /\ sentStartViewChange' = [sentStartViewChange EXCEPT ![r] = {}]
          /\ recievedStartViewChange' = [recievedStartViewChange EXCEPT ![r] = {m.i}]
          /\ UNCHANGED <<lastNormalView, recievedDoViewChangeMsgs>>
       \/ \* Our view number
          /\ m.v = viewNumber[r]
          /\ status[r] = ViewChange
          /\ recievedStartViewChange' = [recievedStartViewChange EXCEPT ![r] = recievedStartViewChange[r] \cup {m.i}]
          /\ UNCHANGED <<replicaViewVars, sentStartViewChange, recievedDoViewChangeMsgs>>
       \/ \* Stale view
          /\ m.v < viewNumber[r]
          /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars>>
    /\ Drop(m)
    /\ UNCHANGED <<clientStateVars, replicaLogVars, replicaExecVars, primaryVars>>

AchieveStartViewChangeFromQuorum(r) ==
    /\ \E Q \in Quorum: /\ r \in Q
                        /\ Q \subseteq recievedStartViewChange[r]
    /\ Send([src |-> r, dst |-> PrimaryReplicaInView(viewNumber[r]),
             type |-> DoViewChange, v |-> viewNumber[r],
             l |-> log[r], vv |-> lastNormalView[r],
             n |-> opNumber[r], k |-> commitNumber[r], i |-> r])
    /\ UNCHANGED <<clientStateVars, replicaStateVars>>

RecieveDoViewChange(p, m) ==
    /\ IsPrimaryInView(p, m.v)
    /\ m.type = DoViewChange
    /\ \/ \* Update view number
          /\ m.v > viewNumber[p]
          /\ viewNumber' = [viewNumber EXCEPT ![p] = m.v]
          /\ status' = [status EXCEPT ![p] = ViewChange]
          /\ recievedDoViewChangeMsgs' = [recievedDoViewChangeMsgs EXCEPT ![p] = {m}]
          /\ UNCHANGED <<lastNormalView, sentStartViewChange, recievedStartViewChange>>
    /\ \/ \* Our view number
          /\ m.v = viewNumber[p]
          /\ status[p] = ViewChange
          /\ recievedDoViewChangeMsgs' = [recievedDoViewChangeMsgs EXCEPT ![p] = recievedDoViewChangeMsgs[p] \cup {m}]
          /\ UNCHANGED <<replicaViewVars, sentStartViewChange, recievedStartViewChange>>
    /\ \/ \* Stale message
          /\ m.v < viewNumber[p]
          /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars>>
    /\ Drop(m)
    /\ UNCHANGED <<clientStateVars, replicaLogVars, replicaExecVars, primaryVars>>

\* Become Primary
AchieveDoViewChangeFromQuorum(p) ==
    /\ \E Q \in Quorum: /\ p \in Q
                        /\ Q \subseteq recievedDoViewChangeMsgs[p]
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
    /\ UNCHANGED <<clientStateVars, viewNumber, lastNormalView, prepared, executedOperations, sentPreparedOpNumber, recievedPrepareOkOpNumber>>

SendStartView(p, r) ==
    /\ IsPrimary(p)
    /\ p # r
    /\ ~ (r \in sentStartView[p])
    /\ Send([src |-> p, dst |-> r, type |-> StartView,
             v |-> viewNumber[p], l |-> log[p], n |-> opNumber[p], k |-> commitNumber[p]])
    /\ sentStartView' = [sentStartView EXCEPT ![p] = sentStartView[p] \cup {r}]
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, sentPreparedOpNumber, recievedPrepareOkOpNumber>>

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
    /\ UNCHANGED <<clientStateVars, replicaViewChangeVars, prepared, executedOperations, primaryVars, msgs>>

-----------------------------------------------------------------------------

Next == \/ \E c \in Client: ClientSendRequest(c)
        \/ \E c \in Client, m \in msgs: RecieveReply(c, m)
        \/ \E r \in Replica, m \in msgs: RecieveClientRequest(r, m)
        \/ \E r \in Replica, m \in msgs: RecievePrepare(r, m)
        \/ \E r \in Replica, m \in msgs: RecieveCommit(r, m)
        \/ \E r \in Replica, m \in msgs: RecievePrepareOk(r, m)
        \/ \E r \in Replica: ExecuteClientRequest(r)
        \/ \E r \in Replica: AchievePrepareOkFromQuorum(r)
        \/ \E p, r \in Replica: SendCommit(p, r)
        \/ \E r \in Replica: TimeoutStartViewChanging(r)
        \/ \E p, r \in Replica: SendStartViewChange(p, r)
        \/ \E r \in Replica, m \in msgs: RecieveStartViewChange(r, m)
        \/ \E r \in Replica: AchieveStartViewChangeFromQuorum(r)
        \/ \E r \in Replica, m \in msgs: RecieveDoViewChange(r, m)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
        \/ \E p, r \in Replica: SendStartView(p, r)
        \/ \E r \in Replica, m \in msgs: RecieveStartView(r, m)

-----------------------------------------------------------------------------

(* Liveness *)

EventuallyRecieveClientRequest == \A r \in Replica: WF_vars(\E m \in msgs: RecieveClientRequest(r, m))

EventuallyRecievePrepare == \A r \in Replica: WF_vars(\E m \in msgs: RecievePrepare(r, m))

EventuallyRecieveCommit == \A r \in Replica: WF_vars(\E m \in msgs: RecieveCommit(r, m))

EventuallyRecievePrepareOk == \A p \in Replica: WF_vars(\E m \in msgs: RecievePrepareOk(p, m))

EventuallyAchievePrepareOkFromQuorum == \A p \in Replica: WF_vars(AchievePrepareOkFromQuorum(p))

EventuallyRecieveReply == \A c \in Client: WF_vars(\E m \in msgs: RecieveReply(c, m))

LivenessSpec ==
    /\ EventuallyRecieveClientRequest
    /\ EventuallyRecievePrepare
    /\ EventuallyRecieveCommit
    /\ EventuallyRecievePrepareOk
    /\ EventuallyAchievePrepareOkFromQuorum
    /\ EventuallyRecieveReply

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

LogsPreficesAreEqual == \A r1, r2 \in Replica: PreficiesAreEqual(log[r1], log[r2])

-----------------------------------------------------------------------------

(* Properties *)

AllClientsWillBeServed == \A c \in Client: (pendingRequest[c] ~> ~pendingRequest[c])



-----------------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Sat Nov 26 16:37:50 MSK 2022 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
