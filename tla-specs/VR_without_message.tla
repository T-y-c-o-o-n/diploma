------------------------- MODULE VR_without_message -------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

Status == {Normal, ViewChange, Recovering}

\* Client operation
CONSTANT Operation

\* types of log blocks
CONSTANTS RequestBlock, ViewBlock

\* Result of executing operation
Result == Operation

RequestNumber == Nat

\* Special value
CONSTANT None

\* Message types for processing client request
CONSTANTS Request

\* Message types for replica recovery
CONSTANTS Recovery, RecoveryResponse

\* Sequence with all replicas (for view selection)
CONSTANT ReplicaSequence

\* State on each replica
VARIABLES viewNumber, status, lastNormalView,
          opNumber, log, commitNumber, prepared,
          executedOperations

\* Persistant state on each replica
VARIABLE recoveryCount

\* State on Primary replica
VARIABLES recievedPrepareOkOpNumber

replicaViewVars == <<viewNumber, status, lastNormalView>>

replicaLogVars == <<opNumber, log>>

replicaExecVars == <<commitNumber, prepared, executedOperations>>

primaryVars == <<recievedPrepareOkOpNumber>>

replicaStateVars == <<replicaViewVars, replicaLogVars, replicaExecVars, primaryVars>>

vars == <<replicaStateVars, recoveryCount>>

-----------------------------------------------------------------------------

View == Nat

OpNumber == Nat

CommitNumber == Nat

RequestMessage == [type: {Request}, op: Operation]

LogEntry == [type: RequestBlock, opNumber: Nat, m: RequestMessage]
       \cup [type: ViewBlock, view: View]

\* All possible messages
Message == [type: {Recovery}, i: Replica, x: Nat]
      \cup [type: {RecoveryResponse}, v: View, x: Nat, l: Seq(LogEntry) \cup {None},
            n: OpNumber \cup {None}, k: CommitNumber \cup {None}, i: Replica, j: Replica]

TypeOK == /\ viewNumber \in [Replica -> View]
          /\ status \in [Replica -> Status]
          /\ lastNormalView \in [Replica -> View]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ commitNumber \in [Replica -> Nat]
          /\ prepared \in [Replica -> Nat]
          /\ executedOperations \in [Replica -> Seq(LogEntry)]
          /\ recievedPrepareOkOpNumber \in [Replica -> [Replica -> OpNumber]]
          /\ recoveryCount \in [Replica -> Nat]

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

ASSUME IsFiniteSet(Replica)

max(S) == CHOOSE x \in S: \A y \in S: y <= x

lastOpNumber(l) == IF l = <<>> THEN 0 ELSE l[Len(l)].opNumber

-----------------------------------------------------------------------------

Init == /\ viewNumber = [r \in Replica |-> 0]
        /\ status = [r \in Replica |-> Normal]
        /\ lastNormalView = [r \in Replica |-> 0]
        /\ opNumber = [r \in Replica |-> 0]
        /\ log = [r \in Replica |-> << >>]
        /\ commitNumber = [r \in Replica |-> 0]
        /\ prepared = [r \in Replica |-> 0]
        /\ executedOperations = [r \in Replica |-> << >>]
        /\ recievedPrepareOkOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
        /\ recoveryCount = [r \in Replica |-> 0]

-----------------------------------------------------------------------------

ExecuteOperation(op) == op

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, viewNumber[r])

AddClientRequest(r, m) ==
    /\ opNumber' = [opNumber EXCEPT ![r] = opNumber[r] + 1]
    /\ log' = [log EXCEPT ![r] = Append(log[r], [type |-> RequestBlock, opNumber |-> opNumber'[r], m |-> m])]

RecieveClientRequestNEW(p, op) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ AddClientRequest(p, [type |-> RequestBlock, op |-> op])
    /\ UNCHANGED <<replicaViewVars, replicaExecVars, primaryVars, recoveryCount>>

RecievePrepareNEW(r) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ status[r] = Normal
    /\ LET primary == PrimaryReplicaInView(viewNumber[r])
       IN /\ \/ viewNumber[primary] > viewNumber[r]  \* TODO it is not fully correct actually
             \/ /\ viewNumber[primary] = viewNumber[r]  \* Here should be "primary was in Normal status in our view and had message"
                /\ status[primary] = Normal
          /\ opNumber[primary] > opNumber[r]
          /\ log[primary][opNumber[r] + 1].type = RequestBlock
          /\ AddClientRequest(r, log[primary][opNumber[r] + 1].m)
    /\ UNCHANGED <<replicaViewVars, replicaExecVars, primaryVars, recoveryCount>>

PrepareOperationNEW(r) ==
    /\ ~IsPrimary(r)
    /\ status[r] = Normal
    /\ prepared[r] < Len(log[r])
    /\ prepared' = [prepared EXCEPT ![r] = prepared[r] + 1]
    /\ UNCHANGED <<replicaViewVars, replicaLogVars, commitNumber, executedOperations, primaryVars, recoveryCount>>

ExecuteRequest(r, entry) ==
    /\ executedOperations' = [executedOperations EXCEPT ![r] = Append(executedOperations[r], entry)]

ExecuteClientRequest(r) ==
    /\ status[r] = Normal
    /\ Len(executedOperations[r]) < commitNumber[r]
    /\ Len(log[r]) >= Len(executedOperations[r]) + 1
    /\ ExecuteRequest(r, log[r][Len(executedOperations[r]) + 1])
    /\ UNCHANGED <<replicaViewVars, replicaLogVars, commitNumber, prepared, primaryVars, recoveryCount>>

AchievePrepareOkFromQuorumNEW(p) ==
    /\ Len(executedOperations[p]) = commitNumber[p]
    /\ LET newCommit == commitNumber[p] + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ recievedPrepareOkOpNumber[p][r] >= newCommit
                     \/ r = p
          /\ commitNumber' = [commitNumber EXCEPT ![p] = newCommit]
          /\ ExecuteRequest(p, log[p][newCommit].m)
    /\ UNCHANGED <<replicaViewVars, replicaLogVars, prepared, primaryVars, recoveryCount>>

CheckAchievePrepareOkFromQuorumNEW(p) ==
    /\ Len(executedOperations[p]) = commitNumber[p]
    /\ LET newCommit == commitNumber[p] + 1
       IN IF /\ \E Q \in Quorum:
                    \A r \in Q:
                        \/ recievedPrepareOkOpNumber'[p][r] >= newCommit
                        \/ r = p
          THEN /\ commitNumber' = [commitNumber EXCEPT ![p] = newCommit]
               /\ ExecuteRequest(p, log[p][newCommit])
               /\ UNCHANGED <<prepared>>
          ELSE /\ UNCHANGED <<replicaExecVars>>

RecievePrepareOkNEW(p, r) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ status[r] = Normal
    /\ viewNumber[r] = viewNumber[p]
    /\ prepared[r] > recievedPrepareOkOpNumber[p][r]
    /\ Len(log[p]) > recievedPrepareOkOpNumber[p][r] + 1
    /\ recievedPrepareOkOpNumber' = [recievedPrepareOkOpNumber EXCEPT ![p][r] = recievedPrepareOkOpNumber[p][r] + 1]
    /\ CheckAchievePrepareOkFromQuorumNEW(p)
    /\ UNCHANGED <<replicaViewVars, replicaLogVars, recoveryCount>>

RecieveCommitNEW(r) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ status[r] = Normal
    /\ \E p \in Replica:
        /\ viewNumber[r] = viewNumber[p]
        /\ IsPrimary(p)
        /\ commitNumber[p] > commitNumber[r]
        \* TODO:set any possible value between commitNumber[r] and commitNumber[r2]
        /\ commitNumber' = [commitNumber EXCEPT ![r] = commitNumber[p]] 
    /\ UNCHANGED <<replicaViewVars, replicaLogVars, prepared, executedOperations, primaryVars, recoveryCount>>

-----------------------------------------------------------------------------

(* View Changing *)

TimeoutStartViewChangingNEW(r) ==
    /\ status[r] = Normal
    /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[r] + 1]
    /\ status' = [status EXCEPT ![r] = ViewChange]
    /\ UNCHANGED <<lastNormalView, replicaLogVars, replicaExecVars, primaryVars, recoveryCount>>

RecieveStartViewChangeNEW(r) ==
    /\ status[r] = Normal
    /\ \E r2 \in Replica:
        /\ viewNumber[r2] > viewNumber[r]
        /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[r2]]
        /\ status' = [status EXCEPT ![r] = ViewChange]
    /\ UNCHANGED <<lastNormalView, replicaLogVars, replicaExecVars, primaryVars, recoveryCount>>

\* Become Primary
AchieveDoViewChangeFromQuorumNEW(p) ==
    /\ IsPrimary(p)
    /\ status[p] = ViewChange
    /\ \E Q \in Quorum:
        /\ p \in Q
        /\ \A r \in Q:
            /\ viewNumber[r] = viewNumber[p]
            /\ status[r] = ViewChange
        /\ LET maxVV == max({lastNormalView[r] : r \in Q})
               maxN == max({opNumber[r] : r \in {r \in Q : lastNormalView[r] = maxVV}})
               maxReplica == CHOOSE r \in Q: lastNormalView[r] = maxVV /\ opNumber[r] = maxN
               newLog == log[maxReplica]
           IN /\ log' = [log EXCEPT ![p] = Append(newLog, [type |-> ViewBlock, view |-> viewNumber[p]])]
              /\ opNumber' = [opNumber EXCEPT ![p] = opNumber[maxReplica]]
              /\ commitNumber' = [commitNumber EXCEPT ![p] = max({commitNumber[r] : r \in Q})]
    /\ status' = [status EXCEPT ![p] = Normal]
    /\ lastNormalView' = [lastNormalView EXCEPT ![p] = viewNumber[p]]
    /\ UNCHANGED <<viewNumber, prepared, executedOperations, recievedPrepareOkOpNumber, recoveryCount>>

RecieveStartViewNEW(r) ==
    /\ \E p \in Replica:
            /\ IsPrimary(p)
            /\ status[p] = Normal
            /\ \/ viewNumber[p] > viewNumber[r]
               \/ /\ viewNumber[p] = viewNumber[r]
                  /\ status[r] = ViewChange
            /\ log' = [log EXCEPT ![r] = log[p]]
            /\ opNumber' = [opNumber EXCEPT ![r] = opNumber[p]]
            /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[p]]
            /\ status' = [status EXCEPT ![r] = Normal]
            /\ lastNormalView' = [lastNormalView EXCEPT ![r] = viewNumber'[r]]
            /\ commitNumber' = [commitNumber EXCEPT ![r] = commitNumber[p]]
            /\ prepared' = [prepared EXCEPT ![r] = commitNumber[p]]
    /\ UNCHANGED <<executedOperations, primaryVars, recoveryCount>>

-----------------------------------------------------------------------------

(* Recovery *)

ReplicaCrashNEW(r) ==
    /\ viewNumber' = [viewNumber EXCEPT! [r] = 0]
    /\ status' = [status EXCEPT! [r] = Recovering]
    /\ lastNormalView' = [lastNormalView EXCEPT! [r] = 0]
    /\ opNumber' = [opNumber EXCEPT! [r] = 0]
    /\ log' = [log EXCEPT! [r] = << >>]
    /\ commitNumber' = [commitNumber EXCEPT! [r] = 0]
    /\ prepared' = [r2 \in Replica |-> 0]
    /\ executedOperations' = [executedOperations EXCEPT! [r] = << >>]
    /\ recievedPrepareOkOpNumber' = [recievedPrepareOkOpNumber EXCEPT! [r] = [r2 \in Replica |-> 0]]
    /\ recoveryCount' = [recoveryCount EXCEPT ![r] = recoveryCount[r] + 1]
(*
RecoveryReceive(r, r2) ==
    /\ status[r] = Normal
    /\ status[r2] = Recovering
    /\ IF IsPrimary(r)
       THEN /\ Send([type |-> RecoveryResponse, v |-> viewNumber[r], x |-> m.x,
                     l |-> log[r], n |-> opNumber[r], k |-> commitNumber[r], i |-> m.i, j |-> r])
       ELSE /\ Send([type |-> RecoveryResponse, v |-> viewNumber[r], x |-> m.x,
                     l |-> None, n |-> None, k |-> None, i |-> m.i, j |-> r])
    /\ UNCHANGED <<replicaStateVars, recoveryCount>>
*)
AchieveRecoveryResponseFromQuorumNEW(r) ==
    /\ status[r] = Recovering
    /\ \E Q \in Quorum:
           /\ \A r2 \in Q: status[r2] = Normal
           /\ LET maxView == max({viewNumber[r2]: r2 \in Q})
                  newLog == log[PrimaryReplicaInView(maxView)]
                  newOpNumber == opNumber[PrimaryReplicaInView(maxView)]
                  newCommitNumber == commitNumber[PrimaryReplicaInView(maxView)]
              IN /\ \E p \in Q: IsPrimaryInView(p, maxView)
                 /\ status' = [status EXCEPT ![r] = Normal]
                 /\ viewNumber' = [viewNumber EXCEPT ![r] = maxView]
                 /\ log' = [log EXCEPT ![r] = newLog]
                 /\ opNumber' = [opNumber EXCEPT ![r] = newOpNumber]
                 /\ lastNormalView' = [lastNormalView EXCEPT ![r] = maxView]
                 /\ commitNumber' = [commitNumber EXCEPT ![r] = newCommitNumber]
                 /\ UNCHANGED <<prepared, executedOperations, primaryVars, recoveryCount>>

-----------------------------------------------------------------------------


Next == \/ \E r \in Replica, op \in Operation: RecieveClientRequestNEW(r, op)
        \/ \E r \in Replica: RecievePrepareNEW(r)
        \/ \E r \in Replica: PrepareOperationNEW(r)
        \/ \E p, r \in Replica: RecievePrepareOkNEW(p, r)
        \/ \E r \in Replica: RecieveCommitNEW(r)
        \/ \E r \in Replica: ExecuteClientRequest(r)
        \/ \E r \in Replica: TimeoutStartViewChangingNEW(r)
        \/ \E r \in Replica: RecieveStartViewChangeNEW(r)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorumNEW(r)
        \/ \E r \in Replica: RecieveStartViewNEW(r)
        \/ \E r \in Replica: ReplicaCrashNEW(r)
        \/ \E r \in Replica: AchieveRecoveryResponseFromQuorumNEW(r)

-----------------------------------------------------------------------------

(* Liveness *)

\*EventuallyRecieveClientRequest == \A r \in Replica: WF_vars(\E op \in Operation: RecieveClientRequest(r, op))

\*EventuallyRecievePrepare == \A r \in Replica: WF_vars(\E m \in msgs: RecievePrepare(r, m))

\*EventuallyRecieveCommit == \A r \in Replica: WF_vars(\E m \in msgs: RecieveCommit(r, m))

\*EventuallyRecievePrepareOk == \A p \in Replica: WF_vars(\E m \in msgs: RecievePrepareOk(p, m))

\*LivenessSpec ==
\*    /\ EventuallyRecieveClientRequest
\*    /\ EventuallyRecievePrepare
\*    /\ EventuallyRecieveCommit
\*    /\ EventuallyRecievePrepareOk

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
\* Last modified Sun Jan 01 19:27:57 MSK 2023 by tycoon
\* Created Wed Dec 28 15:30:37 MSK 2022 by tycoon
