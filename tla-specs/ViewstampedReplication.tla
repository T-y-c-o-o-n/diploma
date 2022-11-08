----------------------- MODULE ViewstampedReplication -----------------------
EXTENDS Integers, Sequences

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

\* state on each replica
VARIABLES viewNumber, status, opNumber, log, commitNumber, clientTable

View == Nat

OpNumber == Nat

CommitNumber == Nat

LogEntry == [op: Operation, opNumber: Nat]

\* Message types for processing client request
CONSTANTS Request, Prepare, PrepareOk, Reply, Commit

\* Message types for view changing
CONSTANTS StartViewChange, DoViewChange, StartView

\* Message types for replica recovery
CONSTANTS Recovery, RecoveryResponse

\* All possible messages
Message ==      [type: {Request}, op: Operation, c: ClientId, s: RequestNumber]
           \cup [type: {Prepare}, v: View, m: [op: Operation,
                                               c: ClientId,
                                               s: RequestNumber],
                 n: OpNumber, k: CommitNumber]
           \cup [type: {PrepareOk}, v: View, n: OpNumber, i: Replica]
           \cup [type: {Reply}, v: View, s: RequestNumber, x: Result]
           \cup [type: {Commit}, v: View, k: CommitNumber]

TypeOK == /\ viewNumber \in [Replica -> View]
          /\ status \in [Replica -> Status]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ commitNumber \in [Replica -> Nat \cup {0}]
          /\ clientTable \in [Replica -> [Client -> [lastReq: Nat \cup {0},
                                                     result: Result \cup {None}]]]


ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 


=============================================================================
\* Modification History
\* Last modified Tue Nov 08 13:15:59 MSK 2022 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
