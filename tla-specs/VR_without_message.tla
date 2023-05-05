------------------------- MODULE VR_without_message -------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

\* Client operation
CONSTANT Operation

\* types of log blocks
CONSTANTS RequestBlock, ViewBlock

\* Special value
CONSTANT None

\* Sequence with all replicas (for view selection)
CONSTANT ReplicaSequence

\* For state space limitation
CONSTANT MaxRequests, MaxViews

\* State on each replica
VARIABLE replicaState

vars == <<replicaState>>

-----------------------------------------------------------------------------

Statuses == {Normal, ViewChange, Recovering}

LogEntry == [type: {RequestBlock}, opNumber: Nat, op: Operation]
       \cup [type: {ViewBlock}, view: Nat]

TypeOK == /\ replicaState \in [
            Replica -> [
                viewNumber: Nat,
                status: Statuses,
                log: Seq(LogEntry),
                downloadReplica: Replica \cup {None},
                commitNumber: Nat
              ]
            ]

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

ASSUME IsFiniteSet(Replica)

Min(S) == CHOOSE x \in S: \A y \in S: x <= y

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

-----------------------------------------------------------------------------

Init == /\ replicaState = [r \in Replica |-> [
                    viewNumber |-> 0,
                    status |-> Normal,
                    log |-> << [type |-> ViewBlock, view |-> 0] >>,
                    downloadReplica |-> None,
                    commitNumber |-> 0
                ]
           ]

-----------------------------------------------------------------------------

ViewNumber(r) == replicaState[r].viewNumber

Status(r) == replicaState[r].status

Log(r) == replicaState[r].log

LogLen(r) == Len(Log(r))

LastNormalView(r) == Max({0} \cup {Log(r)[i].view : i \in {i \in 1 .. LogLen(r) : Log(r)[i].type = ViewBlock}})

OpNumber(r) == LogLen(r)

DownloadReplica(r) == replicaState[r].downloadReplica

CommitNumber(r) == replicaState[r].commitNumber

ReplicaIndex(r) == CHOOSE i \in 1..Cardinality(Replica): ReplicaSequence[i] = r

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, replicaState[r].viewNumber)

IsDownloading(r) ==
    /\ replicaState[r].downloadReplica # None

FirstIndexOfViewBlock(log, v) == Min({Len(log) + 1} \cup {i \in 1 .. Len(log) : log[i].type = ViewBlock /\ log[i].view >= v})

MaxLogEntryInView(log, v) == LET first == FirstIndexOfViewBlock(log, v)
                             IN IF /\ first <= Len(log)
                                   /\ log[first].view = v
                                THEN FirstIndexOfViewBlock(log, v + 1) - 1
                                ELSE 0

HasViewBlock(r, v) == LET ind == FirstIndexOfViewBlock(Log(r), v)
                      IN /\ ind <= LogLen(r)
                         /\ Log(r)[ind].view = v

MaxViewLessOrEq(log, v) == Max({0} \cup {log[i].view : i \in {i \in 1 .. Len(log) : log[i].type = ViewBlock /\ log[i].view <= v}})

MaxOpNumBeforeView(log, v) == FirstIndexOfViewBlock(log, v) - 1

RequestBlockCount(log) == Cardinality({i \in DOMAIN log: log[i].type = RequestBlock})

ViewBlockCount(log) == Cardinality({i \in DOMAIN log: log[i].type = ViewBlock})

-----------------------------------------------------------------------------

(* NORMAL OPERATION *)

AddClientRequest(r, m) ==
    /\ replicaState' = [replicaState EXCEPT ![r].log = Append(@, m)]

RecieveClientRequest(p, op) ==
    /\ RequestBlockCount(Log(p)) < MaxRequests
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloading(p)
    /\ AddClientRequest(p, [type |-> RequestBlock,
                            opNumber |-> OpNumber(p) + 1,
                            op |-> op])

RecievePrepare(r) ==
    /\ RequestBlockCount(Log(r)) < MaxRequests
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloading(r)
          \* Has Replica with saved request from primary
    /\ \/ /\ \E r2 \in Replica:
                 /\ MaxLogEntryInView(Log(r2), ViewNumber(r)) > OpNumber(r)
                 /\ Log(r2)[OpNumber(r) + 1].type = RequestBlock
                 /\ AddClientRequest(r, Log(r2)[OpNumber(r) + 1])
          \* There is no saved request from primary
       \/ /\ \A r2 \in Replica:
                 /\ MaxLogEntryInView(Log(r2), ViewNumber(r)) <= OpNumber(r)
          \* + primary will not generate new Prepare
          /\ LET p == PrimaryReplicaInView(ViewNumber(r))
             IN \/ ViewNumber(p) > ViewNumber(r)
                \/ Status(p) = Recovering
          \* suddenly got old sent request from primary
          /\ \E op \in Operation: AddClientRequest(r, [type |-> RequestBlock,
                                                       opNumber |-> OpNumber(r) + 1,
                                                       op |-> op])

AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloading(p)
    /\ LET newCommit == CommitNumber(p) + 1
       IN /\ \E Q \in Quorum:
                 /\ \A r \in Q: MaxLogEntryInView(Log(r), ViewNumber(p)) >= newCommit
                 /\ p \in Q
          /\ replicaState' = [replicaState EXCEPT ![p].commitNumber = newCommit]

RecieveCommit(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloading(r)
    /\ LET p == PrimaryReplicaInView(ViewNumber(r))
       IN /\ \E newCommit \in CommitNumber(r) + 1 .. Min({LogLen(r), CommitNumber(p)}):  \* think about right border
              /\ \E Q \in Quorum:
                  /\ p \in Q
                  /\ \A r2 \in Q:
                      /\ LogLen(r2) >= newCommit
                      /\ \A i \in CommitNumber(r) + 1 .. newCommit:
                             Log(r2)[i] = Log(r)[i]
              /\ replicaState' = [replicaState EXCEPT ![r].commitNumber = newCommit] 

-----------------------------------------------------------------------------

(* VIEW CHANGING *)

\* -> E1
TimeoutStartViewChanging(r) ==
    /\ ViewNumber(r) + 1 < MaxViews
    /\ Status(r) = Normal
    /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                            ![r].viewNumber = @ + 1,
                                            ![r].status = ViewChange]

\* -> E1
RecieveStartViewChange(r) ==
    /\ \E r2 \in Replica:
        /\ ViewNumber(r2) > ViewNumber(r)
        /\ \E newView \in ViewNumber(r) + 1 .. ViewNumber(r2):
               replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                                    ![r].viewNumber = newView,
                                                    ![r].status = ViewChange]

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
            /\ \/ /\ ViewNumber(r) = ViewNumber(p)
                  /\ Status(r) = ViewChange
                  \* r has already joined to new elections
               \/ /\ ViewNumber(r) > ViewNumber(p)
            \* Can't just take LastNormalView(r) and OpNumber(r), because there are can be saved messages with old state (lastNormalView, opNumber)
            \* And here no such state is saved + other replicas could increase their state
            \*     => maxVV, maxN, maxReplica and new commit can easily differ from WithMsgs Spec
        /\ LET maxVV == Max({MaxViewLessOrEq(Log(r), ViewNumber(p) - 1) : r \in recievedReplicas})
               maxN == Max({MaxOpNumBeforeView(Log(r), ViewNumber(p)) : r \in {r \in recievedReplicas : LastNormalView(r) = maxVV}})
               maxReplicaIndex == Max({ReplicaIndex(r) : r \in {r \in recievedReplicas : LastNormalView(r) = maxVV /\ OpNumber(r) = maxN}})
               maxReplica ==
                      \* If we are suit then choose ourselves  
                   IF /\ maxVV = MaxViewLessOrEq(Log(p), ViewNumber(p) - 1)
                      /\ maxN = MaxOpNumBeforeView(Log(p), ViewNumber(p))
                   THEN p
                   ELSE CHOOSE r \in recievedReplicas: ReplicaIndex(r) = maxReplicaIndex
           IN /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = IF maxReplica = p
                                                                             THEN None
                                                                             ELSE maxReplica,
                                                      ![p].log = IF maxReplica = p
                                                                 THEN Append(@, [type |-> ViewBlock, view |-> ViewNumber(p)])
                                                                 ELSE @,
                                                      ![p].status = Normal]

\* Mc -> Mc / Mc -> M
MasterDownloadBeforeView(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ IsDownloading(p)
    /\ LET finishPos == FirstIndexOfViewBlock(Log(DownloadReplica(p)), ViewNumber(p) + 1) - 1
           entriesToDownload == { i \in CommitNumber(p) + 1 .. finishPos:
                                      \* New entry for r
                                      \/ LogLen(p) < i
                                      \* Diff in logs
                                      \/ Log(p)[i] # Log(DownloadReplica(p))[i] }
       IN /\ entriesToDownload # {}
          /\ LET ind == Min(entriesToDownload)
                 finished == ind = finishPos
             IN /\ replicaState' = [replicaState EXCEPT ![p].log = 
                                                             IF finished
                                                             THEN Append(Append(SubSeq(@, 1, ind - 1), Log(DownloadReplica(p))[ind]), [type |-> ViewBlock, view |-> ViewNumber(p)])
                                                             ELSE Append(SubSeq(@, 1, ind - 1), Log(DownloadReplica(p))[ind]),
                                                        ![p].downloadReplica =
                                                                      IF finished
                                                                      THEN None
                                                                      ELSE @]

\* Er -> Rc
RecieveStartView(r) ==
    /\ \E p \in Replica:
        /\ p # r
        /\ \E view \in ViewNumber(r) .. ViewNumber(p):
           /\ IsPrimaryInView(p, view)
           /\ \/ view > ViewNumber(r)
              \/ /\ ViewNumber(r) = view
                 /\ Status(r) = ViewChange
           /\ HasViewBlock(p, view)  \* p became Normal Master in view
           /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = p,
                                                   ![r].viewNumber = view,
                                                   ![r].status = Normal]

\* Rc -> Rc / Rc -> R
ReplicaDownloadBeforeView(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ IsDownloading(r)
    /\ LET entriesToDownload == { i \in CommitNumber(r) + 1 .. FirstIndexOfViewBlock(Log(DownloadReplica(r)), ViewNumber(r) + 1) - 1:
                                  \* New entry for r
                                  \/ LogLen(r) < i
                                  \* Diff in logs
                                  \/ Log(r)[i] # Log(DownloadReplica(r))[i] }
       IN /\ entriesToDownload # {}
          /\ LET ind == Min(entriesToDownload)
             IN /\ replicaState' = [replicaState EXCEPT ![r].log = Append(SubSeq(@, 1, ind - 1), Log(DownloadReplica(r))[ind]),
                                                        ![r].downloadReplica =
                                                                      \* Have just downloaded our View meta Block
                                                                      IF Log(DownloadReplica(r))[ind] = [type |-> ViewBlock, view |-> ViewNumber(r)] 
                                                                      THEN None
                                                                      ELSE @]

-----------------------------------------------------------------------------

Finishing ==
    /\ LET r == ReplicaSequence[1]
          \* All Committed
       IN /\ CommitNumber(r) = OpNumber(r)
          \* MaxRequests commands are stored
          /\ RequestBlockCount(Log(r)) = MaxRequests
          \* All replicas equal
          /\ \A r1 \in Replica:
                 /\ Log(r1) = Log(r)
                 /\ CommitNumber(r1) = CommitNumber(r)
                 /\ ViewNumber(r1) = ViewNumber(r)
                 /\ Status(r1) = Normal
                 /\ DownloadReplica(r1) = None
    /\ UNCHANGED <<replicaState>>

-----------------------------------------------------------------------------

NormalOperationProtocol ==
    \/ \E r \in Replica, op \in Operation: RecieveClientRequest(r, op)
    \/ \E r \in Replica: RecievePrepare(r)
    \/ \E p \in Replica: AchievePrepareOkFromQuorum(p)
    \/ \E r \in Replica: RecieveCommit(r)

ViewChangeProtocol ==
    \/ \E r \in Replica: TimeoutStartViewChanging(r)
    \/ \E r \in Replica: RecieveStartViewChange(r)
    \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
    \/ \E r \in Replica: RecieveStartView(r)
    \/ \E p \in Replica: MasterDownloadBeforeView(p)
    \/ \E r \in Replica: ReplicaDownloadBeforeView(r)

Next == \/ NormalOperationProtocol
        \/ ViewChangeProtocol
        \/ Finishing

-----------------------------------------------------------------------------

(* Full Spec *)

Spec == Init /\ [][Next]_vars

FullSpec == Spec /\ SF_vars(Next)

-----------------------------------------------------------------------------

(* INVARIANTS *)

CommitedLogsPreficesAreEqual ==
    \A r1, r2 \in Replica:
        \A i \in DOMAIN Log(r1)
            \cap DOMAIN Log(r2)
            \cap 1 .. Min({CommitNumber(r1),
                           CommitNumber(r2)}):
                Log(r1)[i] = Log(r2)[i]

KeepMaxRequests == \A r \in Replica: RequestBlockCount(Log(r)) <= MaxRequests

KeepMaxViews == \A r \in Replica: ViewNumber(r) + 1 <= MaxViews

-----------------------------------------------------------------------------

(* Properties *)

EventuallyFinished == <> (ENABLED Finishing)

-----------------------------------------------------------------------------


=============================================================================
\* Modification History
\* Last modified Fri May 05 13:43:04 MSK 2023 by tycoon
\* Created Wed Dec 28 15:30:37 MSK 2022 by tycoon
