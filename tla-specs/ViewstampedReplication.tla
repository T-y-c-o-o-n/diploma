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
VARIABLES viewNumber, status, lastNormalView, startViewChangeMsgs, doViewChangeMsgs,
          opNumber, log, commitNumber, prepared,
          executedOperations

\* State on Primary replica
VARIABLES sentPreparedOpNumber, recievedPrepareOkOpNumber

\* Clients state
VARIABLES lastRequestId, pendingRequest

VARIABLE msgs

replicaViewVars == <<viewNumber, status, lastNormalView, startViewChangeMsgs, doViewChangeMsgs>>

replicaLogVars == <<opNumber, log>>

replicaExecVars == <<commitNumber, prepared, executedOperations>>

primaryVars == <<sentPreparedOpNumber, recievedPrepareOkOpNumber>>

replicaStateVars == <<replicaViewVars, replicaLogVars, replicaExecVars, primaryVars>>

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
          /\ startViewChangeMsgs \in [Replica -> SUBSET Replica]
          /\ doViewChangeMsgs \in [Replica -> SUBSET Message]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ commitNumber \in [Replica -> Nat]
          /\ prepared \in [Replica -> Nat]
          /\ executedOperations \in [Replica -> Seq(RequestMessage)]
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
        /\ startViewChangeMsgs = [r \in Replica |-> {}]
        /\ doViewChangeMsgs = [r \in Replica |-> {}]
        /\ opNumber = [r \in Replica |-> 0]
        /\ log = [r \in Replica |-> << >>]
        /\ commitNumber = [r \in Replica |-> 0]
        /\ prepared = [r \in Replica |-> 0]
        /\ executedOperations = [r \in Replica |-> << >>]
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

SendPrepare(p, r) ==
    /\ IsPrimary(p)
    /\ p # r
    /\ sentPreparedOpNumber[p][r] < Len(log[p])
    /\ LET sentOpNumber == sentPreparedOpNumber[p][r] + 1
       IN /\ sentPreparedOpNumber' = [sentPreparedOpNumber EXCEPT ![p][r] = sentOpNumber]
          /\ Send([type |-> Prepare, v |-> viewNumber[p], m |-> log[sentOpNumber].m,
             n |-> sentOpNumber, k |-> commitNumber[p]])
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaLogVars, replicaExecVars, recievedPrepareOkOpNumber>>

RecieveClientRequest(r, m) ==
    /\ IsPrimary(r)
    /\ m.type = Request
    /\ AddClientRequest(r, m)
    /\ Drop(m)
    /\ UNCHANGED <<clientStateVars, replicaViewVars, replicaExecVars, primaryVars>>

PrepareOperation(r) ==
    /\ ~IsPrimary(r)
    /\ prepared[r] < Len(log[r])
    /\ prepared' = [prepared EXCEPT ![r] = prepared[r] + 1]
    /\ Send([src |-> r, dst |-> PrimaryReplicaInView(viewNumber[r]), type |-> PrepareOk,
             v |-> viewNumber[r], n |-> log[prepared'[r]].opNumber, i |-> r])
    /\ UNCHANGED <<>>



RecievePrepare(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.type = Prepare
    /\ m.n = opNumber[r] + 1
    /\ AddClientRequest(r, m.m)
    /\ UNCHANGED <<clientStateVars, replicaViewVars, commitNumber, prepared, executedOperations, primaryVars>>

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
    /\ UNCHANGED <<clientStateVars, replicaViewVars, opNumber, log, commitNumber, prepared, executedOperations>>

ExecuteRequest(r, request) ==
    /\ executedOperations' = [executedOperations EXCEPT ![r] = Append(executedOperations[r], request)]

ExecuteClientRequest(r) ==
    /\ Len(executedOperations[r]) < commitNumber[r]
    /\ Len(log[r]) >= Len(executedOperations[r]) + 1
    /\ ExecuteRequest(r, log[r][Len(executedOperations[r]) + 1].m)
    /\ UNCHANGED <<clientStateVars, replicaViewVars, opNumber, log, commitNumber, prepared, primaryVars, msgs>>

AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ \E Q \in Quorum:
           \A r \in Q:
               \/ maxPrepareOkOpNumber[p][r] >= commitNumber[p] + 1
               \/ r = p
    /\ commitNumber' = [commitNumber EXCEPT ![p] = commitNumber[p] + 1]
    /\ ExecuteRequest(p, log[p][commitNumber'[p]].m)
    /\ Send([src |-> p, dst |-> ?, type |-> Reply, v |-> viewNumber[p], s |-> log[p][commitNumber'[p]].m.s,
             x |-> ExecuteOperation(log[p][commitNumber'[p]].op), c |-> log[p][commitNumber'[p]].m.c])
    /\ UNCHANGED <<clientStateVars, replicaViewVars, opNumber, log, prepared, primaryVars>>

SendCommit(p) ==
    /\ IsPrimary(p)
    /\ Send([src |-> r, dst |-> ?, type |-> Commit, v |-> viewNumber[p], k |-> commitNumber[p]])
    /\ UNCHANGED <<clientStateVars, replicaStateVars>>

RecieveCommit(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.type = Commit
    /\ m.k > commitNumber[r]
    /\ commitNumber' = [commitNumber EXCEPT ![r] = m.k]
    /\ Drop(m)  \* TODO: don't remove or send to every replica different messages
    /\ UNCHANGED<<clientStateVars, viewNumber, status, lastNormalView, doViewChangeMsgs, startViewChangeMsgs, opNumber, log, prepared, executedOperations, primaryVars>>

-----------------------------------------------------------------------------

(* View Changing *)

\* TODO: add cases for StartViewChanging
StartViewChanging(r) ==
    /\ status[r] = Normal
    /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[r] + 1]
    /\ status' = [status EXCEPT ![r] = ViewChange]
       \* Send to one replica
    /\ Send([src |-> r, dst |-> ?, type |-> StartViewChange, v |-> viewNumber'[r], i |-> r])
    /\ UNCHANGED <<clientStateVars, lastNormalView, doViewChangeMsgs, startViewChangeMsgs, opNumber, log, commitNumber, prepared, executedOperations, primaryVars>>

RecieveStartViewChange(r, m) ==
    \* TODO: check status ?
    /\ m.type = StartViewChange
    /\ m.v = viewNumber[r]
    /\ startViewChangeMsgs' = [startViewChangeMsgs EXCEPT ![r] = startViewChangeMsgs[r] \cup {m.i}]
    /\ UNCHANGED <<clientStateVars, viewNumber, status, lastNormalView, doViewChangeMsgs, opNumber, log, commitNumber, prepared, executedOperations, primaryVars, msgs>>

AchieveStartViewChangeFromQuorum(r) ==
    /\ \E Q \in Quorum: (Q \cup {r}) \subseteq startViewChangeMsgs[r]
    /\ Send([src |-> r, dst |-> PrimaryReplicaInView(viewNumber[r]),
             type |-> DoViewChange, v |-> viewNumber[r],
             l |-> log[r], vv |-> lastNormalView[r],
             n |-> opNumber[r], k |-> commitNumber[r], i |-> r])
    /\ UNCHANGED <<clientStateVars, replicaStateVars>>


RecieveDoViewChange(p, m) ==
    /\ IsPrimaryInView(p, viewNumber[p])
    /\ status[p] = ViewChange
    /\ m.type = DoViewChange
    /\ m.v = viewNumber[p]
    /\ doViewChangeMsgs' = [doViewChangeMsgs EXCEPT ![p] = doViewChangeMsgs[p] \cup {m}]
    /\ UNCHANGED <<clientStateVars, viewNumber, status, lastNormalView, startViewChangeMsgs, opNumber, log, commitNumber, prepared, executedOperations, primaryVars, msgs>>

\* Become Primary
AchieveDoViewChangeFromQuorum(p) ==
    /\ \E Q \in Quorum: \/ Q \subseteq doViewChangeMsgs[p]
                        \/ p \in doViewChangeMsgs[p]
    /\ LET maxVV == max({m.vv : m \in doViewChangeMsgs[p]})
           maxN == max({m.n : m \in {m \in doViewChangeMsgs[p] : m.vv = maxVV}})
           maxMsg == CHOOSE m \in doViewChangeMsgs[p]: m.vv = maxVV /\ m.n = maxN
           newLog == maxMsg.l
       IN /\ log' = [log EXCEPT ![p] = newLog]
          /\ opNumber' = [opNumber EXCEPT ![p] = lastOpNumber(newLog)]
    /\ commitNumber' = [commitNumber EXCEPT ![p] = max({m.k : m \in doViewChangeMsgs[p]})]
    /\ status' = [status EXCEPT ![p] = Normal]
    /\ lastNormalView' = [lastNormalView EXCEPT ![p] = viewNumber[p]]
    /\ Send([src |-> p, dst |-> ?, type |-> StartView, v |-> viewNumber[p],
             l |-> log'[p], n |-> opNumber'[p], k |-> commitNumber'[p]])
    /\ UNCHANGED <<clientStateVars, viewNumber, startViewChangeMsgs, doViewChangeMsgs, prepared, executedOperations, primaryVars>>

RecieveStartView(r, m) ==
    /\ m.type = StartView
    /\ m.v >= viewNumber[r]
    /\ log' = [log EXCEPT ![r] = m.l]
    /\ opNumber' = [opNumber EXCEPT ![r] = m.n]
    /\ viewNumber' = [viewNumber EXCEPT ![r] = m.v]
    /\ status' = [status EXCEPT ![r] = Normal]
    /\ commitNumber' = [commitNumber EXCEPT ![r] = m.k]
    /\ prepared' = [prepared EXCEPT ![r] = m.k]
    /\ UNCHANGED <<clientStateVars, lastNormalView, startViewChangeMsgs, doViewChangeMsgs, executedOperations, primaryVars, msgs>>

-----------------------------------------------------------------------------

Next == \/ \E c \in Client: ClientSendRequest(c)
        \/ \E c \in Client, m \in msgs: RecieveReply(c, m)
        \/ \E r \in Replica, m \in msgs: RecieveClientRequest(r, m)
        \/ \E r \in Replica, m \in msgs: RecievePrepare(r, m)
        \/ \E r \in Replica, m \in msgs: RecieveCommit(r, m)
        \/ \E r \in Replica, m \in msgs: RecievePrepareOk(r, m)
        \/ \E r \in Replica: ExecuteClientRequest(r)
        \/ \E r \in Replica: AchievePrepareOkFromQuorum(r)
        \/ \E r \in Replica: SendCommit(r)
        \/ \E r \in Replica, m \in msgs: StartViewChanging(r)
        \/ \E r \in Replica, m \in msgs: RecieveStartViewChange(r, m)
        \/ \E r \in Replica: AchieveStartViewChangeFromQuorum(r)
        \/ \E r \in Replica, m \in msgs: RecieveDoViewChange(r, m)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
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
\* Last modified Fri Nov 25 17:53:24 MSK 2022 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
