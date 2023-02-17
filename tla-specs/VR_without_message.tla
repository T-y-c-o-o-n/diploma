------------------------- MODULE VR_without_message -------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

Statuses == {Normal, ViewChange, Recovering}

\* Client operation
CONSTANT Operation

\* types of log blocks
CONSTANTS RequestBlock, ViewBlock

\* Special value
CONSTANT None

\* Message types for processing client request
CONSTANTS Request

\* Message types for replica recovery
CONSTANTS Recovery, RecoveryResponse

\* Sequence with all replicas (for view selection)
CONSTANT ReplicaSequence

(*
\* State on each replica
VARIABLES viewNumber, status, lastNormalView,
          opNumber, log, downloadReplica,
          commitNumber, prepared, executedOperations
*)
\* Persistant state on each replica
VARIABLE recoveryCount

\* State on each replica
VARIABLE replicaState

\* State on Primary replica
\*VARIABLES recievedPrepareOkOpNumber

\* TODO: replace with one struct with all replica fields

(*
replicaViewVars == <<viewNumber, status, lastNormalView>>

replicaLogVars == <<opNumber, log, downloadReplica>>

replicaExecVars == <<commitNumber, prepared, executedOperations>>

primaryVars == <<recievedPrepareOkOpNumber>>

replicaStateVars == <<replicaViewVars, replicaLogVars, replicaExecVars, primaryVars>>
*)

vars == <<replicaState, recoveryCount>>

-----------------------------------------------------------------------------

View == Nat

RequestMessage == [type: {Request}, op: Operation]

LogEntry == [type: RequestBlock, opNumber: Nat, m: RequestMessage]
       \cup [type: ViewBlock, view: View]

\* All possible messages
Message == [type: {Recovery}, i: Replica, x: Nat]
      \cup [type: {RecoveryResponse}, v: View, x: Nat, l: Seq(LogEntry) \cup {None},
            n: Nat \cup {None}, k: Nat \cup {None}, i: Replica, j: Replica]

TypeOK == /\ recoveryCount \in [Replica -> Nat]
          /\ replicaState \in [
            Replica -> [
                viewNumber: View,
                status: Statuses,
                lastNormalView: View,
                opNumber: Nat,
                log: Seq(LogEntry),
                downloadReplica: Replica \cup {None},
                commitNumber: Nat,
                prepared: Nat,
                executedOperations: Seq(LogEntry),
                recievedPrepareOkOpNumber: [Replica -> Nat]
              ]
            ]
          (*/\ viewNumber \in [Replica -> View]
          /\ status \in [Replica -> Status]
          /\ lastNormalView \in [Replica -> View]
          /\ opNumber \in [Replica -> Nat]
          /\ log \in [Replica -> Seq(LogEntry)]
          /\ downloadReplica \in [Replica -> Replica \cup {None}]
          /\ commitNumber \in [Replica -> Nat]
          /\ prepared \in [Replica -> Nat]
          /\ executedOperations \in [Replica -> Seq(LogEntry)]
          /\ recievedPrepareOkOpNumber \in [Replica -> [Replica -> OpNumber]]*)

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

ASSUME IsFiniteSet(Replica)

Min(S) == CHOOSE x \in S: \A y \in S: x <= y

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

lastOpNumber(l) == IF l = <<>> THEN 0 ELSE l[Len(l)].opNumber

-----------------------------------------------------------------------------

Init == /\ replicaState = [r \in Replica |-> [
                    viewNumber |-> 0,
                    status |-> Normal,
                    lastNormalView |-> 0,
                    opNumber |-> 0,
                    log |-> << >>,
                    downloadReplica |-> None,
                    commitNumber |-> 0,
                    prepared |-> 0,
                    executedOperations |-> << >>,
                    recievedPrepareOkOpNumber |-> [r1 \in Replica |-> 0]
                ]
           ]
        /\ recoveryCount = [r \in Replica |-> 0]
(*        /\ status = [r \in Replica |-> Normal]
        /\ lastNormalView = [r \in Replica |-> 0]
        /\ opNumber = [r \in Replica |-> 0]
        /\ log = [r \in Replica |-> << >>]
        /\ downloadReplica = [r \in Replica |-> None]
        /\ commitNumber = [r \in Replica |-> 0]
        /\ prepared = [r \in Replica |-> 0]
        /\ executedOperations = [r \in Replica |-> << >>]
        /\ recievedPrepareOkOpNumber = [p \in Replica |-> [r \in Replica |-> 0]] *)

-----------------------------------------------------------------------------

ViewNumber(r) == replicaState[r].viewNumber

Status(r) == replicaState[r].status

LastNormalView(r) == replicaState[r].lastNormalView

OpNumber(r) == replicaState[r].commitNumber

Log(r) == replicaState[r].log

LogLen(r) == Len(Log(r))

DownloadReplica(r) == replicaState[r].downloadReplica

CommitNumber(r) == replicaState[r].commitNumber

Prepared(r) == replicaState[r].prepared

ExecutedOperations(r) == replicaState[r].executedOperations

RecievedPrepareOkOpNumber(r) == replicaState[r].recievedPrepareOkOpNumber

ExecuteOperation(op) == op

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, replicaState[r].viewNumber)

IsDownloadingBeforeView(r) ==
    /\ replicaState[r].downloadReplica # None

AddClientRequest(r, m) ==
    /\ replicaState' = [replicaState EXCEPT ![r].opNumber = @ + 1,
                                            ![r].log = Append(@, [
                                                type |-> RequestBlock,
                                                opNumber |-> replicaState[r].opNumber + 1,
                                                m |-> m
                                              ])]

RecieveClientRequest(p, op) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ AddClientRequest(p, [type |-> RequestBlock, op |-> op])
    /\ UNCHANGED <<recoveryCount>>

RecievePrepare(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ LET primary == PrimaryReplicaInView(ViewNumber(r))
       IN /\ ViewNumber(primary) = ViewNumber(r)  \* Here should be "primary was in Normal status in our view and had message"
          /\ Status(primary) = Normal
          /\ LogLen(primary) > LogLen(r)
          /\ Log(primary)[LogLen(r) + 1].type = RequestBlock
          /\ AddClientRequest(r, Log(primary)[LogLen(r) + 1].m)
    /\ UNCHANGED <<recoveryCount>>

PrepareOperation(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ Prepared(r) < Len(Log(r))
    /\ replicaState' = [replicaState EXCEPT ![r].prepared = @ + 1]
    /\ UNCHANGED <<recoveryCount>>

ExecuteRequest(r, entry) ==
    /\ replicaState' = [replicaState EXCEPT ![r].executedOperations = Append(@, entry)]

ExecuteClientRequest(r) ==
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ Len(ExecutedOperations(r)) < CommitNumber(r)
    /\ Len(ExecutedOperations(r)) < Len(Log(r))
    /\ ExecuteRequest(r, Log(r)[Len(ExecutedOperations(r)) + 1])
    /\ UNCHANGED <<recoveryCount>>

AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ ~IsDownloadingBeforeView(p)
    /\ Len(ExecutedOperations(p)) = CommitNumber(p)
    /\ LET newCommit == CommitNumber(p) + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ RecievedPrepareOkOpNumber(p)[r] >= newCommit
                     \/ r = p
          /\ replicaState' = [replicaState EXCEPT ![p].commitNumber = newCommit,
                                                  ![p].executedOperations = Append(@, Log(p)[newCommit])]  \* ExecuteRequest(p, Log(p)[newCommit])
    /\ UNCHANGED <<recoveryCount>>
(*
CheckAchievePrepareOkFromQuorum(p, r) ==
    /\ ~IsDownloadingBeforeView(p)
    /\ Len(ExecutedOperations(p)) = CommitNumber(p)
    /\ LET newCommit == CommitNumber(p) + 1
       IN IF /\ \E Q \in Quorum:
                    \A r1 \in Q:
                        \/ replicaState'[p].recievedPrepareOkOpNumber[r1] >= newCommit
                        \/ r1 = p
          THEN /\ replicaState' = [replicaState EXCEPT ![p].commitNumber = newCommit,
                                                       ![p].recievedPrepareOkOpNumber[r] = @ + 1]
               /\ ExecuteRequest(p, Log(p)[newCommit])
          ELSE /\ replicaState' = [replicaState EXCEPT ![p].recievedPrepareOkOpNumber[r] = @ + 1]
*)
RecievePrepareOk(p, r) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ ViewNumber(r) = ViewNumber(p)
    /\ Prepared(r) > RecievedPrepareOkOpNumber(p)[r]
    /\ LogLen(p) > RecievedPrepareOkOpNumber(p)[r]
    /\ replicaState' = [replicaState EXCEPT ![p].recievedPrepareOkOpNumber[r] = @ + 1]
    /\ UNCHANGED <<recoveryCount>>

RecieveCommit(r) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ \E p \in Replica:
        /\ ViewNumber(r) = ViewNumber(p)
        /\ IsPrimary(p)
        /\ CommitNumber(p) > CommitNumber(r)
        \* TODO:set any possible value between commitNumber[r] and commitNumber[r2]
        /\ replicaState' = [replicaState EXCEPT ![r].commitNumber = CommitNumber(p)] 
    /\ UNCHANGED <<recoveryCount>>

-----------------------------------------------------------------------------

(* View Changing *)

\* -> E1
TimeoutStartViewChanging(r) ==
    /\ Status(r) = Normal
    /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                            ![r].viewNumber = @ + 1,
                                            ![r].status = ViewChange]
    /\ UNCHANGED <<recoveryCount>>

\* -> E1
RecieveStartViewChange(r) ==
    /\ Status(r) = Normal
    /\ \E r2 \in Replica:
        /\ ViewNumber(r2) > ViewNumber(r)
        /\ Status(r2) = ViewChange
        /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                                ![r].viewNumber = ViewNumber(r2),
                                                ![r].status = ViewChange]
    /\ UNCHANGED <<recoveryCount>>

\* TODO: ADD ->Er and ->Em states and transitions

\* Become Primary
\* Em -> Mc
AchieveDoViewChangeFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = ViewChange
    /\ \E Q \in Quorum:
        /\ p \in Q
        /\ \A r \in Q:
            /\ ViewNumber(r) = ViewNumber(p)
            /\ Status(r) = ViewChange
        /\ LET maxVV == Max({LastNormalView(r) : r \in Q})
               maxN == Max({OpNumber(r) : r \in {r \in Q : LastNormalView(r) = maxVV}})
               maxReplica == CHOOSE r \in Q: LastNormalView(r) = maxVV /\ OpNumber(r) = maxN
               \* newLog == log[maxReplica]
           IN /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = maxReplica,
                                                      ![p].commitNumber = Max({CommitNumber(r) : r \in Q}),
                                                      ![p].status = Normal,
                                                      ![p].lastNormalView = ViewNumber(p)]
    /\ UNCHANGED <<recoveryCount>>

\* Mc -> Mc / Mc -> M
MasterDownloadBeforeView(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ IsDownloadingBeforeView(p)
    /\ ViewNumber(p) = ViewNumber(DownloadReplica(p))  \* If replica will increase view, then this Primary could only start view changing
    /\ LogLen(p) < LogLen(DownloadReplica(p))
    /\ LET newEntry == Log(DownloadReplica(p))[LogLen(p) + 1]
       IN \/ /\ LogLen(p) + 1 = LogLen(DownloadReplica(p))
             /\ replicaState' = [replicaState EXCEPT ![p].log = Append(Append(@, newEntry), [type |-> ViewBlock, view |-> ViewNumber(p)]),
                                                     ![p].opNumber = @ + 1,
                                                     ![p].downloadReplica = None]
          \/ /\ replicaState' = [replicaState EXCEPT ![p].log = Append(@, newEntry),
                                                     ![p].opNumber = @ + 1]
    /\ UNCHANGED <<recoveryCount>>

\* Append(newLog, [type |-> ViewBlock, view |-> viewNumber[p]])

\* Er -> Rc
\* TODO: setup download up to View metablock
RecieveStartView(r) ==
    /\ \E p \in Replica:
            /\ IsPrimary(p)
            /\ Status(p) = Normal
            /\ ~IsDownloadingBeforeView(p)
            /\ \/ ViewNumber(p) > ViewNumber(r)
               \/ /\ ViewNumber(p) = ViewNumber(r)
                  /\ Status(r) = ViewChange
            /\ replicaState' = [replicaState EXCEPT ![r].log = SubSeq(Log(r), 1, Min({LogLen(r), CommitNumber(r)})),
                                                    ![r].downloadReplica = p,
                                                    ![r].viewNumber = ViewNumber(p),
                                                    ![r].status = Normal,
                                                    ![r].lastNormalView = ViewNumber(p),
                                                    ![r].commitNumber = CommitNumber(p),
                                                    ![r].prepared = CommitNumber(p)]
    /\ UNCHANGED <<recoveryCount>>

\* Rc -> Rc / Rc -> R
ReplicaDownloadBeforeView(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ IsDownloadingBeforeView(r)
    /\ IF LogLen(DownloadReplica(r)) <= LogLen(r)
       THEN /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None]
       ELSE LET newEntry == Log(DownloadReplica(r))[LogLen(r) + 1]
            IN /\ replicaState' = [replicaState EXCEPT ![r].log = Append(@, newEntry),
                                                       ![r].opNumber = @ + 1,
                                                       ![r].downloadReplica =
                                                            IF newEntry = [type |-> ViewBlock, view |-> ViewNumber(r)]  \* Have just downloaded View meta Block 
                                                            THEN None
                                                            ELSE @]
    /\ UNCHANGED <<recoveryCount>>

-----------------------------------------------------------------------------

(* Recovery *)

ReplicaCrash(r) ==
    /\ replicaState' = [replicaState EXCEPT ![r].status = Recovering,
                                            ![r].viewNumber = 0,
                                            ![r].lastNormalView = 0,
                                            ![r].opNumber = 0,
                                            ![r].log = << >>,
                                            ![r].commitNumber = 0,
                                            ![r].prepared = 0,
                                            ![r].executedOperations = << >>,
                                            ![r].recievedPrepareOkOpNumber = [r2 \in Replica |-> 0],
                                            ![r].downloadReplica = None]
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
AchieveRecoveryResponseFromQuorum(r) ==
    /\ Status(r) = Recovering
    /\ \E Q \in Quorum:
           /\ \A r2 \in Q: Status(r2) = Normal
           /\ LET maxView == Max({ViewNumber(r2): r2 \in Q})
                  newLog == Log(PrimaryReplicaInView(maxView))
                  newOpNumber == OpNumber(PrimaryReplicaInView(maxView))
                  newCommitNumber == CommitNumber(PrimaryReplicaInView(maxView))
              IN /\ \E p \in Q: IsPrimaryInView(p, maxView)
                 /\ replicaState' = [replicaState EXCEPT ![r].status = Normal,
                                                         ![r].viewNumber = maxView,
                                                         ![r].log = newLog,
                                                         ![r].opNumber = newOpNumber,
                                                         ![r].lastNormalView = maxView,
                                                         ![r].commitNumber = newCommitNumber]
                 /\ UNCHANGED <<recoveryCount>>

-----------------------------------------------------------------------------


Next == \/ \E r \in Replica, op \in Operation: RecieveClientRequest(r, op)
        \/ \E r \in Replica: RecievePrepare(r)
        \/ \E r \in Replica: PrepareOperation(r)
        \/ \E p, r \in Replica: RecievePrepareOk(p, r)
        \/ \E p \in Replica: AchievePrepareOkFromQuorum(p)
        \/ \E r \in Replica: RecieveCommit(r)
        \/ \E r \in Replica: ExecuteClientRequest(r)
        \/ \E r \in Replica: TimeoutStartViewChanging(r)
        \/ \E r \in Replica: RecieveStartViewChange(r)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
        \/ \E r \in Replica: RecieveStartView(r)
        \/ \E r \in Replica: ReplicaCrash(r)
        \/ \E r \in Replica: AchieveRecoveryResponseFromQuorum(r)
        \/ \E p \in Replica: MasterDownloadBeforeView(p)
        \/ \E r \in Replica: ReplicaDownloadBeforeView(r)

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

ExecutedOperationsPreficesAreEqual == \A r1, r2 \in Replica: PreficiesAreEqual(ExecutedOperations(r1), ExecutedOperations(r2))

PreficiesOfLenAreEqual(s1, s2, prefLen) == \A i \in DOMAIN s1 \cap DOMAIN s2 \cap 1..prefLen: s1[i] = s2[i]

CommitedLogsPreficesAreEqual == \A r1, r2 \in Replica: PreficiesOfLenAreEqual(Log(r1), Log(r2), Min({CommitNumber(r1), CommitNumber(r2)}))

-----------------------------------------------------------------------------

(* Properties *)

\*AllClientsWillBeServed == \A c \in Client: (pendingRequest[c] ~> ~pendingRequest[c])



-----------------------------------------------------------------------------


=============================================================================
\* Modification History
\* Last modified Thu Feb 16 20:08:04 MSK 2023 by tycoon
\* Created Wed Dec 28 15:30:37 MSK 2022 by tycoon
