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

LogEntry == [type: {RequestBlock}, opNumber: Nat, m: RequestMessage]
       \cup [type: {ViewBlock}, view: View]

\* All possible messages
Message == [type: {Recovery}, i: Replica, x: Nat]
      \cup [type: {RecoveryResponse}, v: View, x: Nat, l: Seq(LogEntry) \cup {None},
            n: Nat \cup {None}, k: Nat \cup {None}, i: Replica, j: Replica]

TypeOK == /\ recoveryCount \in [Replica -> Nat]
          /\ replicaState \in [
            Replica -> [
                viewNumber: View,
                status: Statuses,
                log: Seq(LogEntry),
                downloadReplica: Replica \cup {None},
                commitNumber: Nat,
                executedOperations: Seq(LogEntry)
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
                    log |-> << [type |-> ViewBlock, view |-> 0] >>,
                    downloadReplica |-> None,
                    commitNumber |-> 0,
                    executedOperations |-> << >>
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

Log(r) == replicaState[r].log

LogLen(r) == Len(Log(r))

LastNormalView(r) == Max({0} \cup {Log(r)[i].view : i \in {i \in 1 .. LogLen(r) : Log(r)[i].type = ViewBlock}})

OpNumber(r) == LogLen(r)

DownloadReplica(r) == replicaState[r].downloadReplica

CommitNumber(r) == replicaState[r].commitNumber

ExecutedOperations(r) == replicaState[r].executedOperations

ExecuteOperation(op) == op

ReplicaIndex(r) == CHOOSE i \in 1..Cardinality(Replica): ReplicaSequence[i] = r

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, replicaState[r].viewNumber)

IsDownloadingBeforeView(r) ==
    /\ replicaState[r].downloadReplica # None

AddClientRequest(r, m) ==
    /\ replicaState' = [replicaState EXCEPT ![r].log = Append(@, [
                                                type |-> RequestBlock,
                                                opNumber |-> OpNumber(r) + 1,
                                                m |-> m
                                              ])]

RecieveClientRequest(p, op) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ AddClientRequest(p, [type |-> Request, op |-> op])
    /\ UNCHANGED <<recoveryCount>>

FirstIndexOfViewBlock(log, v) == Min({Len(log) + 1} \cup {i \in 1 .. Len(log) : log[i].type = ViewBlock /\ log[i].view >= v})

MaxLogEntryInView(log, v) == LET first == FirstIndexOfViewBlock(log, v)
                             IN IF /\ first <= Len(log)
                                   /\ log[first].view = v
                                THEN FirstIndexOfViewBlock(log, v + 1) - 1
                                ELSE 0

RecievePrepare(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ LET primary == PrimaryReplicaInView(ViewNumber(r))
       IN \* /\ ViewNumber(primary) = ViewNumber(r)  \* Here should be "primary was in Normal status in our view and had message"
          \* /\ Status(primary) = Normal
          /\ \/ /\ MaxLogEntryInView(Log(primary), ViewNumber(r)) > LogLen(r)
                /\ Log(primary)[LogLen(r) + 1].type = RequestBlock
                /\ AddClientRequest(r, Log(primary)[LogLen(r) + 1].m)
                \* Recieved Prepare when Primary has already rejected his log entries, for example after recieving StartView
             \/ /\ MaxLogEntryInView(Log(primary), ViewNumber(r)) = LogLen(r)
                /\ ViewNumber(primary) > ViewNumber(r)
                /\ \E op \in Operation: AddClientRequest(r, [type |-> Request, op |-> op])
    /\ UNCHANGED <<recoveryCount>>

(*
PrepareOperation(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ Prepared(r) < Len(Log(r))
    /\ replicaState' = [replicaState EXCEPT ![r].prepared = @ + 1]
    /\ UNCHANGED <<recoveryCount>>
*)

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
    /\ Status(p) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ Len(ExecutedOperations(p)) = CommitNumber(p)
    /\ LET newCommit == CommitNumber(p) + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ MaxLogEntryInView(Log(r), ViewNumber(p)) >= newCommit
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

(*
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
*)

RecieveCommit(r) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ \E p \in Replica:
       \E newCommit \in CommitNumber(r) + 1 .. Min({LogLen(r), CommitNumber(p)}):
           /\ CommitNumber(p) > CommitNumber(r)
           /\ \E Q \in Quorum:
               /\ p \in Q
               /\ \A r2 \in Q:
                   /\ LogLen(r2) >= newCommit
                   /\ Log(r2)[newCommit] = Log(r)[newCommit]
           /\ replicaState' = [replicaState EXCEPT ![r].commitNumber = newCommit] 
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
        /\ \E newView \in ViewNumber(r) + 1 .. ViewNumber(r2):
               replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                                    ![r].viewNumber = newView,
                                                    ![r].status = ViewChange]
    /\ UNCHANGED <<recoveryCount>>

\* TODO: ADD ->Er and ->Em states and transitions

\* Become Primary
\* Em -> Mc
AchieveDoViewChangeFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = ViewChange
    /\ \E Q \in Quorum, recievedReplicas \in SUBSET Replica:
        /\ p \in Q
        /\ Q \subseteq recievedReplicas
        /\ \A r \in recievedReplicas:
            \* Problem with WithMsg Spec, because other replicas could start new View
            /\ ViewNumber(r) = ViewNumber(p)
            /\ Status(r) = ViewChange
            \* Problem with WithMsg Spec, because there are can be saved messages with old state (lastNormalView, opNumber, commitNumber)
            \* And here no such state is saved + other replicas could increase their state
            \*     => maxVV, maxN, maxReplica and new commit can easily differ from WithMsgs Spec
        /\ LET maxVV == Max({LastNormalView(r) : r \in recievedReplicas})
               maxN == Max({OpNumber(r) : r \in {r \in recievedReplicas : LastNormalView(r) = maxVV}})
               maxReplicaIndex == Max({ReplicaIndex(r) : r \in {r \in recievedReplicas : LastNormalView(r) = maxVV /\ OpNumber(r) = maxN}})
               maxReplica == CHOOSE r \in recievedReplicas: ReplicaIndex(r) = maxReplicaIndex
           IN /\ replicaState' = [replicaState EXCEPT ![p].log = IF maxReplica = p THEN Log(p) ELSE SubSeq(Log(p), 1, Min({LogLen(p), CommitNumber(p)})),
                                                      ![p].downloadReplica = maxReplica,
                                                      ![p].commitNumber = Max({CommitNumber(r) : r \in recievedReplicas}),
                                                      ![p].status = Normal]
    /\ UNCHANGED <<recoveryCount>>

\* Mc -> Mc / Mc -> M
MasterDownloadBeforeView(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ IsDownloadingBeforeView(p)
    /\ ViewNumber(p) = ViewNumber(DownloadReplica(p))  \* If replica will increase view, then this Primary could only start view changing
    /\ LogLen(p) <= LogLen(DownloadReplica(p))
    /\ \/ /\ LogLen(p) = LogLen(DownloadReplica(p))
          /\ replicaState' = [replicaState EXCEPT ![p].log = Append(@, [type |-> ViewBlock, view |-> ViewNumber(p)]),
                                                  ![p].downloadReplica = None]
       \/ /\ LogLen(p) < LogLen(DownloadReplica(p))
          /\ replicaState' = [replicaState EXCEPT ![p].log = Append(@, Log(DownloadReplica(p))[LogLen(p) + 1])]
    /\ UNCHANGED <<recoveryCount>>

\* Append(newLog, [type |-> ViewBlock, view |-> viewNumber[p]])

\* Er -> Rc
\* TODO: setup download up to View metablock
RecieveStartView(r) ==
    /\ \E p \in Replica:
            /\ IsPrimary(p)
            /\ Status(p) = Normal
            /\ ~IsDownloadingBeforeView(p)
            \* Problem with WithMsgs Spec if p has already increased view
            /\ \/ ViewNumber(p) > ViewNumber(r)
               \/ /\ ViewNumber(p) = ViewNumber(r)
                  /\ Status(r) = ViewChange
            /\ replicaState' = [replicaState EXCEPT ![r].log = SubSeq(Log(r), 1, Min({LogLen(r), CommitNumber(r)})),
                                                    ![r].downloadReplica = p,
                                                    ![r].viewNumber = ViewNumber(p),
                                                    ![r].status = Normal]
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
                                            ![r].log = << >>,
                                            ![r].commitNumber = 0,
                                            ![r].executedOperations = << >>,
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
                                                         ![r].commitNumber = newCommitNumber]
                 /\ UNCHANGED <<recoveryCount>>

-----------------------------------------------------------------------------


Next == \/ \E r \in Replica, op \in Operation: RecieveClientRequest(r, op)
        \/ \E r \in Replica: RecievePrepare(r)
\*        \/ \E r \in Replica: PrepareOperation(r)
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
\* Last modified Wed Apr 05 18:08:20 MSK 2023 by tycoon
\* Created Wed Dec 28 15:30:37 MSK 2022 by tycoon
