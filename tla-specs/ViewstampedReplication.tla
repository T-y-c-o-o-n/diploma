----------------------- MODULE ViewstampedReplication -----------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Client, Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

Status == {Normal, ViewChange, Recovering}

\* Client operation
CONSTANT Operation

\* Result of executing operation
CONSTANT Result

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

\* State on each replica
VARIABLES replicaNumber, viewNumber, status, opNumber, log, commitNumber, clientTable

\* Clients state
VARIABLES lastClientRequestId

VARIABLE msgs

replicaStateVars == <<viewNumber, status, opNumber, log, commitNumber, clientTable>>

vars == <<replicaStateVars, msgs>>

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

TypeOK == /\ replicaNumber \in [Replica -> Nat]
          /\ viewNumber \in [Replica -> View]
          /\ status \in [Replica -> Status]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ commitNumber \in [Replica -> Nat \cup {0}]
          /\ clientTable \in [Replica -> [Client -> [lastReq: Nat \cup {0},
                                                     result: Result \cup {None}]]]
          /\ msgs \in SUBSET Message

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

ASSUME IsFiniteSet(Replica)

-----------------------------------------------------------------------------

LastOpNumber(replicaLog) == IF replicaLog = {} THEN 0 ELSE replicaLog[Cardinality(replicaLog)].opNumber

\* Think how to implement it
GenerateOperation == CHOOSE op : op \in Operation

ClientSendRequest(c) ==
    \* TODO: add per Client state with last request id, operation status, e.t.c...
    /\ lastClientRequestId' = lastClientRequestId + 1
    /\ Send([
        type |-> Request, op |-> GenerateOperation,
        (*TODO: save info in client state*)
        c |-> c, s |-> lastClientRequestId'])
    /\ UNCHANGED <<replicaStateVars>>

PrimaryReplicaInView(v) == CHOOSE r : /\ r \in Replica
                                      /\ replicaNumber[r] = v % Cardinality(Replica)

IsPrimary(r) == PrimaryReplicaInView(viewNumber[r]) = r

HandleClientRequest(r, m) ==
    /\ opNumber' = [opNumber EXCEPT ![r] = opNumber[r] + 1]
    /\ log' = Append(log[r], [opNumber |-> opNumber', m |-> m])
    /\ clientTable = [clientTable EXCEPT ![r][m.c] = [lastReq |-> m.s, result |-> None]]
    /\ Send([type |-> Prepare, v |-> viewNumber[r], m |-> m, n |-> opNumber', k |-> commitNumber[r]])
    /\ UNCHANGED <<lastClientRequestId, viewNumber, status, commitNumber, clientTable>>

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
    /\ ~IsPrimary(r)
    /\ m.n = LastOpNumber(log[r]) + 1
    \* TODO continue

=============================================================================
\* Modification History
\* Last modified Wed Nov 09 00:05:17 MSK 2022 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
