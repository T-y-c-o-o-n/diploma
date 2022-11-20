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
VARIABLES viewNumber, status, opNumber, log, commitNumber,
          clientTable, executedOperations, maxPrepareOkOpNumber

\* Clients state
VARIABLES lastRequestId, pendingRequest

VARIABLE msgs

replicaStateVars == <<viewNumber, status,
                      opNumber, log, commitNumber,
                      clientTable, executedOperations, maxPrepareOkOpNumber>>

clientStateVars == <<lastRequestId, pendingRequest>>

vars == <<clientStateVars, replicaStateVars, msgs>>

-----------------------------------------------------------------------------

View == Nat

OpNumber == Nat

CommitNumber == Nat

RequestMessage == [type: {Request}, op: Operation, c: Client, s: RequestNumber]

\* All possible messages
Message ==      RequestMessage
           \cup [type: {Prepare}, v: View, m: RequestMessage, n: OpNumber, k: CommitNumber]
           \cup [type: {PrepareOk}, v: View, n: OpNumber, i: Replica]
           \cup [type: {Reply}, v: View, s: RequestNumber, x: Result, c: Client]
           \cup [type: {Commit}, v: View, k: CommitNumber]

LogEntry == [opNumber: Nat, m: RequestMessage]

\* TODO: add losing, dublicating, out of order messages
Send(m) == msgs' = msgs \cup {m}

Drop(m) == 
    /\ m \in msgs
    /\ msgs' = msgs \ {m}

ReplyMessage(request, response) ==
    /\ request \in msgs
    /\ msgs' = (msgs \ {request}) \cup {response}

TypeOK == /\ lastRequestId \in [Client -> Nat]
          /\ pendingRequest \in [Client -> BOOLEAN]
          /\ viewNumber \in [Replica -> View]
          /\ status \in [Replica -> Status]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ commitNumber \in [Replica -> Nat]
          /\ clientTable \in [Replica -> [Client -> [lastReq: Nat,
                                                     result: Result \cup {None}]]]
          /\ executedOperations \in [Replica -> Seq(RequestMessage)]
          /\ maxPrepareOkOpNumber \in [Replica -> [Replica -> OpNumber]]
          /\ msgs \in SUBSET Message

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

ASSUME IsFiniteSet(Replica)

-----------------------------------------------------------------------------

Init == /\ lastRequestId = [c \in Client |-> 0]
        /\ pendingRequest = [c \in Client |-> FALSE]
        /\ viewNumber = [r \in Replica |-> 0]
        /\ status = [r \in Replica |-> Normal]
        /\ opNumber = [r \in Replica |-> 0]
        /\ log = [r \in Replica |-> << >>]
        /\ commitNumber = [r \in Replica |-> 0]
        /\ clientTable = [r \in Replica |-> [c \in Client |-> [lastReq |-> 0,
                                                               result |-> None]]]
        /\ executedOperations = [r \in Replica |-> << >>]
        /\ maxPrepareOkOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
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
        (*TODO: save info in client state*)
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
    /\ clientTable' = [clientTable EXCEPT ![r][m.c] = [lastReq |-> m.s, result |-> None]]

HandleClientRequest(r, m) ==
    /\ AddClientRequest(r, m)
    /\ ReplyMessage(m, [type |-> Prepare, v |-> viewNumber[r], m |-> m, n |-> opNumber'[r], k |-> commitNumber[r]])

RecieveClientRequest(r, m) ==
    /\ IsPrimary(r)
    /\ m.type = Request
    /\ \/ \* drop stale request
          /\ m.s < clientTable[r][m.c].lastReq
          /\ Drop(m)
          /\ UNCHANGED <<replicaStateVars>>
       \/ \* last request but no result
          /\ m.s > clientTable[r][m.c].lastReq
          /\ HandleClientRequest(r, m)
          /\ UNCHANGED <<viewNumber, status, commitNumber, executedOperations, maxPrepareOkOpNumber>>
       \/ \* resend result
          /\ m.s = clientTable[r][m.c].lastReq
          /\ clientTable[r][m.c].result # None
             \* Should we resend current view or view which was after the operation execution ??
             \* Here I send current view but we can save in clientTable the view after the execution
          /\ ReplyMessage(m, [type |-> Reply, v |-> viewNumber[r], s |-> m.s, x |-> clientTable[r][m.c].result, c |-> m.c])
          /\ UNCHANGED <<replicaStateVars>>
    /\ UNCHANGED <<clientStateVars>>

RecievePrepare(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.type = Prepare
    /\ m.n = opNumber[r] + 1
    /\ AddClientRequest(r, m.m)
    /\ Send([type |-> PrepareOk, v |-> viewNumber[r], n |-> m.n, i |-> r])
    /\ UNCHANGED <<clientStateVars, viewNumber, status, commitNumber, executedOperations, maxPrepareOkOpNumber>>

RecievePrepareOk(p, r, m) ==
    /\ p # r
    /\ IsPrimary(p)
    /\ m.type = PrepareOk
    /\ m.i = r
    /\ \/ \* stale prepareOkMessage
          /\ m.n <= maxPrepareOkOpNumber[p][r]
          /\ UNCHANGED <<maxPrepareOkOpNumber>>
       \/ \* 
          /\ m.n > maxPrepareOkOpNumber[p][r]
          /\ maxPrepareOkOpNumber' = [maxPrepareOkOpNumber EXCEPT ![p][r] = m.n]
    /\ Drop(m)
    /\ UNCHANGED <<clientStateVars, viewNumber, status, opNumber, log, commitNumber, clientTable, executedOperations>>

ExecuteRequest(r, request) ==
    /\ executedOperations' = [executedOperations EXCEPT ![r] = Append(executedOperations[r], request)]
    /\ clientTable' = [clientTable EXCEPT ![r][request.c] = [lastReq |-> request.s,
                                                        result |-> ExecuteOperation(request.op)]]

ExecuteClientRequest(r) ==
    /\ Len(executedOperations[r]) < commitNumber[r]
    /\ Len(log[r]) >= Len(executedOperations[r]) + 1
    /\ ExecuteRequest(r, log[r][Len(executedOperations[r]) + 1].m)
    /\ UNCHANGED <<clientStateVars, viewNumber, status, opNumber, log, commitNumber, maxPrepareOkOpNumber, msgs>>

AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ \E Q \in Quorum:
           \A r \in Q:
               \/ maxPrepareOkOpNumber[p][r] >= commitNumber[p] + 1
               \/ r = p
    /\ commitNumber' = [commitNumber EXCEPT ![p] = commitNumber[p] + 1]
    /\ ExecuteRequest(p, log[p][commitNumber'[p]].m)
    /\ Send([type |-> Reply, v |-> viewNumber[p], s |-> log[p][commitNumber'[p]].m.s, x |-> clientTable'[p][log[p][commitNumber'[p]].m.c].result, c |-> log[p][commitNumber'[p]].m.c])
    /\ UNCHANGED <<clientStateVars, viewNumber, status, opNumber, log, maxPrepareOkOpNumber>>

SendCommit(p) ==
    /\ IsPrimary(p)
    /\ Send([type |-> Commit, v |-> viewNumber[p], k |-> commitNumber[p]])
    /\ UNCHANGED <<clientStateVars, replicaStateVars>>

RecieveCommit(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.type = Commit
    /\ m.k > commitNumber[r]
    /\ commitNumber' = [commitNumber EXCEPT ![r] = m.k]
    /\ Drop(m)  \* TODO: don't remove or send to every replica different messages
    /\ UNCHANGED<<clientStateVars, viewNumber, status, opNumber, log, clientTable, executedOperations, maxPrepareOkOpNumber>>

Next == \/ \E c \in Client: ClientSendRequest(c)
        \/ \E m \in msgs, c \in Client: RecieveReply(c, m)
        \/ \E m \in msgs: \E r \in Replica: RecieveClientRequest(r, m)
        \/ \E m \in msgs, r \in Replica: RecievePrepare(r, m)
        \/ \E m \in msgs, r \in Replica: RecieveCommit(r, m)
        \/ \E m \in msgs, p, r \in Replica: RecievePrepareOk(p, r, m)
        \/ \E r \in Replica: ExecuteClientRequest(r)
        \/ \E r \in Replica: AchievePrepareOkFromQuorum(r)
        \/ \E r \in Replica: SendCommit(r)

-----------------------------------------------------------------------------

(* Liveness *)

EventuallyRecieveClientRequest == \A r \in Replica: WF_vars(\E m \in msgs: RecieveClientRequest(r, m))

EventuallyRecievePrepare == \A r \in Replica: WF_vars(\E m \in msgs: RecievePrepare(r, m))

EventuallyRecieveCommit == \A r \in Replica: WF_vars(\E m \in msgs: RecieveCommit(r, m))

EventuallyRecievePrepareOk == \A p, r \in Replica: WF_vars(\E m \in msgs: RecievePrepareOk(p, r, m))

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

Spec == Init /\ [][Next]_vars /\ LivenessSpec

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

CLientWillRecieveReply == \A c \in Client: (pendingRequest[c] ~> ~pendingRequest[c])

-----------------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Sun Nov 20 15:27:49 MSK 2022 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
