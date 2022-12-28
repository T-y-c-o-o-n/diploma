------------------------- MODULE VR_without_message -------------------------
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

\* Persistant state on each replica
VARIABLE recoveryCount

\* State on Primary replica
VARIABLES (*sentPreparedOpNumber, *)recievedPrepareOkOpNumber(*, sentCommitNumber, sentStartView*)

\* State on View Changing replica
VARIABLES (*sentStartViewChange, *)recievedStartViewChange, recievedDoViewChangeMsgs

VARIABLE msgs

replicaViewVars == <<viewNumber, status, lastNormalView>>

replicaViewChangeVars == <<(*sentStartViewChange, *)recievedStartViewChange, recievedDoViewChangeMsgs>>

replicaLogVars == <<opNumber, log>>

replicaExecVars == <<commitNumber, prepared, executedOperations>>

primaryVars == <<(*sentPreparedOpNumber, *)recievedPrepareOkOpNumber(*, sentCommitNumber, sentStartView*)>>

replicaStateVars == <<replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars>>

vars == <<replicaStateVars, recoveryCount, msgs>>

-----------------------------------------------------------------------------

View == Nat

OpNumber == Nat

CommitNumber == Nat

RequestMessage == [type: {Request}, op: Operation]

LogEntry == [opNumber: Nat, m: RequestMessage]

\* All possible messages
Message == [type: {Prepare}, v: View, m: RequestMessage, n: OpNumber, k: CommitNumber]
      \cup [type: {PrepareOk}, v: View, n: OpNumber, i: Replica]
      \cup [type: {Commit}, v: View, k: CommitNumber]
      \cup [type: {StartViewChange}, v: View, i: Replica]
      \cup [type: {DoViewChange}, v: View, l: Seq(LogEntry), vv: View,
            n: OpNumber, k: CommitNumber, i: Replica]
      \cup [type: {StartView}, v: View, l: Seq(LogEntry), n: OpNumber, k: CommitNumber]
      \cup [type: {Recovery}, i: Replica, x: Nat]
      \cup [type: {RecoveryResponse}, v: View, x: Nat, l: Seq(LogEntry) \cup {None},
            n: OpNumber \cup {None}, k: CommitNumber \cup {None}, i: Replica, j: Replica]

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
\*          /\ sentStartViewChange \in [Replica -> SUBSET Replica]
          /\ recievedStartViewChange \in [Replica -> SUBSET Replica]
          /\ recievedDoViewChangeMsgs \in [Replica -> SUBSET Message]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ commitNumber \in [Replica -> Nat]
          /\ prepared \in [Replica -> Nat]
          /\ executedOperations \in [Replica -> Seq(RequestMessage)]
\*          /\ sentPreparedOpNumber \in [Replica -> [Replica -> OpNumber]]
          /\ recievedPrepareOkOpNumber \in [Replica -> [Replica -> OpNumber]]
\*          /\ sentCommitNumber \in [Replica -> [Replica -> CommitNumber]]
\*          /\ sentStartView \in [Replica -> SUBSET Replica]
          /\ recoveryCount \in [Replica -> Nat]
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
\*        /\ sentStartViewChange = [r \in Replica |-> {}]
        /\ recievedStartViewChange = [r \in Replica |-> {}]
        /\ recievedDoViewChangeMsgs = [r \in Replica |-> {}]
        /\ opNumber = [r \in Replica |-> 0]
        /\ log = [r \in Replica |-> << >>]
        /\ commitNumber = [r \in Replica |-> 0]
        /\ prepared = [r \in Replica |-> 0]
        /\ executedOperations = [r \in Replica |-> << >>]
\*        /\ sentPreparedOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
        /\ recievedPrepareOkOpNumber = [p \in Replica |-> [r \in Replica |-> 0]]
\*        /\ sentCommitNumber = [p \in Replica |-> [r \in Replica |-> 0]]
\*        /\ sentStartView = [r \in Replica |-> {}]
        /\ recoveryCount = [r \in Replica |-> 0]
        /\ msgs = {}

-----------------------------------------------------------------------------

ExecuteOperation(op) == op

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, viewNumber[r])

AddClientRequest(r, m) ==
    /\ opNumber' = [opNumber EXCEPT ![r] = opNumber[r] + 1]
    /\ log' = [log EXCEPT ![r] = Append(log[r], [opNumber |-> opNumber'[r], m |-> m])]

RecieveClientRequestNEW(p, op) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    /\ AddClientRequest(p, [type |-> Request, op |-> op])
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaExecVars, primaryVars, recoveryCount, msgs>>

RecievePrepareNEW(r) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ status[r] = Normal
    /\ LET primary == PrimaryReplicaInView(viewNumber[r])
       IN /\ \/ viewNumber[primary] > viewNumber[r]  \* TODO it is not fully correct actually
             \/ /\ viewNumber[primary] = viewNumber[r]  \* Here should be "primary was in Normal status in our view and had message"
                /\ status[primary] = Normal
          /\ opNumber[primary] > opNumber[r]
          /\ AddClientRequest(r, log[primary][opNumber[r] + 1].m)
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaExecVars, primaryVars, recoveryCount, msgs>>

PrepareOperationNEW(r) ==
    /\ ~IsPrimary(r)
    /\ status[r] = Normal
    /\ prepared[r] < Len(log[r])
    /\ prepared' = [prepared EXCEPT ![r] = prepared[r] + 1]
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, commitNumber, executedOperations, primaryVars, recoveryCount, msgs>>

ExecuteRequest(r, request) ==
    /\ executedOperations' = [executedOperations EXCEPT ![r] = Append(executedOperations[r], request)]

ExecuteClientRequest(r) ==
    /\ status[r] = Normal
    /\ Len(executedOperations[r]) < commitNumber[r]
    /\ Len(log[r]) >= Len(executedOperations[r]) + 1
    /\ ExecuteRequest(r, log[r][Len(executedOperations[r]) + 1].m)
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, commitNumber, prepared, primaryVars, recoveryCount, msgs>>

AchievePrepareOkFromQuorumNEW(p) ==
    /\ Len(executedOperations[p]) = commitNumber[p]
    /\ LET newCommit == commitNumber[p] + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ recievedPrepareOkOpNumber[p][r] >= newCommit
                     \/ r = p
          /\ commitNumber' = [commitNumber EXCEPT ![p] = newCommit]
          /\ ExecuteRequest(p, log[p][newCommit].m)
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, prepared, primaryVars, recoveryCount, msgs>>

CheckAchievePrepareOkFromQuorumNEW(p) ==
    /\ Len(executedOperations[p]) = commitNumber[p]
    /\ LET newCommit == commitNumber[p] + 1
       IN IF /\ \E Q \in Quorum:
                    \A r \in Q:
                        \/ recievedPrepareOkOpNumber'[p][r] >= newCommit
                        \/ r = p
          THEN /\ commitNumber' = [commitNumber EXCEPT ![p] = newCommit]
               /\ ExecuteRequest(p, log[p][newCommit].m)
               /\ UNCHANGED <<prepared>>
          ELSE /\ UNCHANGED <<replicaExecVars>>

RecievePrepareOkNEW(p, r) ==
    /\ IsPrimary(p)
    /\ status[p] = Normal
    \* we don't know, if r prepared our request or from new primary or old
    /\ viewNumber[r] = viewNumber[p]
    /\ prepared[r] > recievedPrepareOkOpNumber[p][r]
    /\ Len(log[p]) > recievedPrepareOkOpNumber[p][r] + 1
    /\ recievedPrepareOkOpNumber' = [recievedPrepareOkOpNumber EXCEPT ![p][r] = recievedPrepareOkOpNumber[p][r] + 1]
    /\ CheckAchievePrepareOkFromQuorumNEW(p)
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, recoveryCount, msgs(*, sentPreparedOpNumber, sentCommitNumber, sentStartView*)>>

RecieveCommitNEW(r) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ status[r] = Normal
    /\ \E r2 \in Replica:
        /\commitNumber[r2] > commitNumber[r]
        \* TODO:set any possible value between commitNumber[r] and commitNumber[r2]
        /\ commitNumber' = [commitNumber EXCEPT ![r] = commitNumber[r2]] 
    /\ UNCHANGED <<replicaViewVars, replicaViewChangeVars, replicaLogVars, prepared, executedOperations, primaryVars, recoveryCount, msgs>>

-----------------------------------------------------------------------------

(* View Changing *)

TimeoutStartViewChangingNEW(r) ==
    /\ status[r] = Normal
    /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[r] + 1]
    /\ status' = [status EXCEPT ![r] = ViewChange]
\*    /\ Send([type |-> StartViewChange, v |-> viewNumber'[r], i |-> r])
    /\ UNCHANGED <<lastNormalView, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars, recoveryCount, msgs>>

RecieveStartViewChangeNEW(r) ==
    /\ \E r2 \in Replica:
        /\ viewNumber[r2] > viewNumber[r]
        /\ viewNumber' = [viewNumber EXCEPT ![r] = viewNumber[r2]]
        /\ status' = [status EXCEPT ![r] = ViewChange]
    /\ UNCHANGED <<lastNormalView, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars, recoveryCount, msgs>>

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
           IN /\ log' = [log EXCEPT ![p] = newLog]
              /\ opNumber' = [opNumber EXCEPT ![p] = lastOpNumber(newLog)]
              /\ commitNumber' = [commitNumber EXCEPT ![p] = max({commitNumber[r] : r \in Q})]
    /\ status' = [status EXCEPT ![p] = Normal]
    /\ lastNormalView' = [lastNormalView EXCEPT ![p] = viewNumber[p]]
    /\ UNCHANGED <<viewNumber, replicaViewChangeVars, prepared, executedOperations, recievedPrepareOkOpNumber, recoveryCount, msgs>>

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
    /\ UNCHANGED <<replicaViewChangeVars, executedOperations, primaryVars, recoveryCount, msgs>>

-----------------------------------------------------------------------------

(* Recovery *)

ReplicaCrash(r) ==
    /\ viewNumber' = [viewNumber EXCEPT! [r] = 0]
    /\ status' = [status EXCEPT! [r] = Recovering]
    /\ lastNormalView' = [lastNormalView EXCEPT! [r] = 0]
    /\ recievedStartViewChange' = [recievedStartViewChange EXCEPT! [r] = {}]
    /\ recievedDoViewChangeMsgs' = [recievedDoViewChangeMsgs EXCEPT! [r] = {}]
    /\ opNumber' = [opNumber EXCEPT! [r] = 0]
    /\ log' = [log EXCEPT! [r] = << >>]
    /\ commitNumber' = [commitNumber EXCEPT! [r] = 0]
    /\ prepared' = [r2 \in Replica |-> 0]
    /\ executedOperations' = [executedOperations EXCEPT! [r] = << >>]
    /\ recievedPrepareOkOpNumber' = [recievedPrepareOkOpNumber EXCEPT! [r] = [r2 \in Replica |-> 0]]
    /\ recoveryCount' = [recoveryCount EXCEPT ![r] = recoveryCount[r] + 1]
    /\ Send([type |-> Recovery, i |-> r, x |-> recoveryCount'[r]])

RecoveryReceive(r, m) ==
    /\ status[r] = Normal
    /\ m.type = Recovery
    /\ IF IsPrimary(r)
       THEN /\ Send([type |-> RecoveryResponse, v |-> viewNumber[r], x |-> m.x,
                     l |-> log[r], n |-> opNumber[r], k |-> commitNumber[r], i |-> m.i, j |-> r])
       ELSE /\ Send([type |-> RecoveryResponse, v |-> viewNumber[r], x |-> m.x,
                     l |-> None, n |-> None, k |-> None, i |-> m.i, j |-> r])
    /\ UNCHANGED <<replicaStateVars, recoveryCount>>

AchieveRecoveryResponseFromQuorum(r) ==
    /\ status[r] = Recovering
    /\ \E Q \in Quorum:
           LET recRespMsgs == {m \in msgs: m.type = RecoveryResponse /\ m.i = r /\ m.x = recoveryCount[r]}
               maxView == max({m.v: m \in recRespMsgs})
               newLog == CHOOSE l \in {m.l: m \in recRespMsgs}: l # None
               newOpNumber == CHOOSE n \in {m.n: m \in recRespMsgs}: n # None
               newCommitNumber == CHOOSE k \in {m.k: m \in recRespMsgs}: k # None
           IN /\ Q = {m.j: m \in recRespMsgs}
              /\ \E r2 \in Q: IsPrimaryInView(r2, maxView)
              /\ status' = [status EXCEPT ![r] = Normal]
              /\ viewNumber' = [viewNumber EXCEPT ![r] = maxView]
              /\ log' = [log EXCEPT ![r] = newLog]
              /\ opNumber' = [opNumber EXCEPT ![r] = newOpNumber]
              /\ lastNormalView' = [lastNormalView EXCEPT ![r] = maxView]
              /\ commitNumber' = [commitNumber EXCEPT ![r] = newCommitNumber]
              /\ UNCHANGED <<replicaViewChangeVars, prepared, executedOperations, primaryVars, recoveryCount, msgs>>

-----------------------------------------------------------------------------


Next == \/ \E r \in Replica, op \in Operation: RecieveClientRequestNEW(r, op)
        \/ \E r \in Replica: RecievePrepareNEW(r)
        \/ \E r \in Replica: PrepareOperationNEW(r)
        \/ \E p, r \in Replica: RecievePrepareOkNEW(p, r)
        \/ \E r \in Replica: RecieveCommitNEW(r)
        \/ \E r \in Replica: ExecuteClientRequest(r)
        \/ \E r \in Replica: TimeoutStartViewChangingNEW(r)
        \/ \E r \in Replica: RecieveStartViewChangeNEW(r)
\*        \/ \E p \in Replica, m \in msgs: RecieveDoViewChange(p, m)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorumNEW(r)
        \/ \E r \in Replica: RecieveStartViewNEW(r)
        \/ \E r \in Replica: ReplicaCrash(r)
        \/ \E r \in Replica, m \in msgs: RecoveryReceive(r, m)
        \/ \E r \in Replica: AchieveRecoveryResponseFromQuorum(r)

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
\* Last modified Wed Dec 28 15:37:04 MSK 2022 by tycoon
\* Created Wed Dec 28 15:30:37 MSK 2022 by tycoon
