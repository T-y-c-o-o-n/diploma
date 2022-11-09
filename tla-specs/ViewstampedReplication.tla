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

CONSTANT replicaNumber

\* State on each replica
VARIABLES viewNumber, status, opNumber, log, commitNumber,
          clientTable, executedOperations, maxPrepareOkOpNumber

\* Clients state
VARIABLES lastClientRequestId

VARIABLE msgs

replicaStateVars == <<viewNumber, status,
                      opNumber, log, commitNumber,
                      clientTable, executedOperations, maxPrepareOkOpNumber>>

vars == <<lastClientRequestId, replicaStateVars, msgs>>

-----------------------------------------------------------------------------

View == Nat

OpNumber == Nat

CommitNumber == Nat

RequestMessage == [type: {Request}, op: Operation, c: Client, s: RequestNumber]

\* All possible messages
Message ==      RequestMessage
           \cup [type: {Prepare}, v: View, m: RequestMessage, n: OpNumber, k: CommitNumber]
           \cup [type: {PrepareOk}, v: View, n: OpNumber, i: Replica]
           \cup [type: {Reply}, v: View, s: RequestNumber, x: Result]
           \cup [type: {Commit}, v: View, k: CommitNumber]

LogEntry == [opNumber: Nat, m: RequestMessage]

Send(m) == msgs' = msgs \cup {m}

Drop(m) == 
    /\ m \in msgs'
    /\ msgs' = msgs \ {m}

TypeOK == /\ lastClientRequestId = 0
          /\ replicaNumber \in [Replica -> Nat]
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

Init ==
    /\ TRUE

-----------------------------------------------------------------------------

\* Think how to implement it
GenerateOperation == CHOOSE op : op \in Operation

Execute(op) == op

PrimaryReplicaInView(v) == CHOOSE r : /\ r \in Replica
                                      /\ replicaNumber[r] = v % Cardinality(Replica)

IsPrimary(r) == PrimaryReplicaInView(viewNumber[r]) = r

ClientSendRequest(c) ==
    \* TODO: add per Client state with operation status, e.t.c...
    /\ lastClientRequestId' = lastClientRequestId + 1
    /\ Send([
        type |-> Request, op |-> GenerateOperation,
        (*TODO: save info in client state*)
        c |-> c, s |-> lastClientRequestId'])
    /\ UNCHANGED <<replicaStateVars>>

AddClientRequest(r, m) ==
    /\ opNumber' = [opNumber EXCEPT ![r] = opNumber[r] + 1]
    /\ log' = Append(log[r], [opNumber |-> opNumber', m |-> m])
    /\ clientTable' = [clientTable EXCEPT ![r][m.c] = [lastReq |-> m.s, result |-> None]]


HandleClientRequest(r, m) ==
    /\ AddClientRequest(r, m)
    /\ Send([type |-> Prepare, v |-> viewNumber[r], m |-> m, n |-> opNumber', k |-> commitNumber[r]])

RecieveClientRequest(r, m) ==
    /\ IsPrimary(r)
    /\ m \in msgs /\ m.type = Request
    /\ \/ \* drop stale request
          /\ m.s < clientTable[r].lastReq
          /\ UNCHANGED <<replicaStateVars>>
       \/ \* last request but no result
          /\ m.s = clientTable[r].lastReq
          /\ clientTable[r].result = None
          /\ HandleClientRequest(r, m)
          /\ UNCHANGED <<viewNumber, status, commitNumber, executedOperations, maxPrepareOkOpNumber>>
       \/ \* resend result
          /\ m.s = clientTable[r].lastReq
          /\ clientTable[r].result # None
             \* Should we resend current view or view which was after the operation execution ??
             \* Here I send current view but we can save in clientTable the view after the execution
          /\ Send([type |-> Reply, v |-> viewNumber[r], s |-> m.s, x |-> clientTable[r].result])
          /\ UNCHANGED <<replicaStateVars>>
       \/ \* request number higher then we know...
          /\ m.s > clientTable[r].lastReq
          /\ UNCHANGED <<replicaStateVars>>
    /\ Drop(m)
    /\ UNCHANGED <<lastClientRequestId>>

RecievePrepare(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.n = opNumber[r] + 1
    /\ AddClientRequest(r, m)
    /\ Send([type |-> PrepareOk, v |-> viewNumber[r], n |-> opNumber[r], i |-> r])
    /\ UNCHANGED <<lastClientRequestId, viewNumber, status, commitNumber, executedOperations, maxPrepareOkOpNumber>>

RecievePrepareOk(p, r, m) ==
    /\ p # r
    /\ IsPrimary(p)
    /\ m.type = PrepareOk
    /\ m.i = r
    /\ \/ \* stale prepareOkMessage
          /\ m.n <= maxPrepareOkOpNumber[p][r]
       \/ \* 
          /\ m.n > maxPrepareOkOpNumber[p][r]
          /\ maxPrepareOkOpNumber' = [maxPrepareOkOpNumber EXCEPT ![p][r] = maxPrepareOkOpNumber[p][r] + 1]
    /\ Drop(m)
    /\ UNCHANGED <<lastClientRequestId, viewNumber, status, opNumber, log, commitNumber, clientTable, executedOperations, msgs>>

ExecuteClientRequest(r) ==
    /\ Len(executedOperations) < commitNumber[r]
    /\ LET request == log[r][Len(executedOperations) + 1].m
       IN /\ executedOperations' = [executedOperations EXCEPT ![r] = Append(executedOperations[r], request)]
          /\ clientTable' = [clientTable EXCEPT ![r] = [lastReq |-> request.s,
                                                        result |-> Execute(request.op)]]
    /\ UNCHANGED <<lastClientRequestId, viewNumber, status, opNumber, log, commitNumber, maxPrepareOkOpNumber, msgs>>

RecievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ \E Q \in Quorum:
           \A r \in Q:
               /\ maxPrepareOkOpNumber[p][r] >= commitNumber[p] + 1
    /\ commitNumber' = [commitNumber EXCEPT ![p] = commitNumber[p] + 1]
    /\ UNCHANGED <<lastClientRequestId, viewNumber, status, opNumber, log, clientTable, executedOperations, maxPrepareOkOpNumber, msgs>>

SendCommit(p) ==
    /\ IsPrimary(p)
    /\ Send([type |-> Commit, v |-> viewNumber, k |-> commitNumber[p]])
    /\ UNCHANGED <<lastClientRequestId, replicaStateVars>>

RecieveCommit(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ m.type = Commit
    /\ m.k > commitNumber[r]
    /\ commitNumber' = [commitNumber EXCEPT ![r] = m.k]
    /\ Drop(m)
    /\ UNCHANGED<<lastClientRequestId, viewNumber, status, opNumber, log, clientTable, executedOperations, maxPrepareOkOpNumber>>



=============================================================================
\* Modification History
\* Last modified Wed Nov 09 23:23:13 MSK 2022 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
