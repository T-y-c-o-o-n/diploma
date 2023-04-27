------------------------- MODULE VR_without_message -------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

\* Client operation
CONSTANT Operation

\* types of log blocks
CONSTANTS RequestBlock, ViewBlock

\* State on each replica
VARIABLE replicaState

vars == <<replicaState>>

\* Special value
CONSTANT None

\* Message types for processing client request
CONSTANTS Request

\* Sequence with all replicas (for view selection)
CONSTANT ReplicaSequence

Statuses == {Normal, ViewChange, Recovering}

-----------------------------------------------------------------------------

View == Nat

LogEntry == [type: {RequestBlock}, opNumber: Nat, op: Operation]
       \cup [type: {ViewBlock}, view: View]

TypeOK == /\ replicaState \in [
            Replica -> [
                viewNumber: View,
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

lastOpNumber(l) == IF l = <<>> THEN 0 ELSE l[Len(l)].opNumber

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

FirstIndexOfViewBlock(log, v) == Min({Len(log) + 1} \cup {i \in 1 .. Len(log) : log[i].type = ViewBlock /\ log[i].view >= v})

MaxLogEntryInView(log, v) == LET first == FirstIndexOfViewBlock(log, v)
                             IN IF /\ first <= Len(log)
                                   /\ log[first].view = v
                                THEN FirstIndexOfViewBlock(log, v + 1) - 1
                                ELSE 0

HasViewBlock(r, v) == LET ind == FirstIndexOfViewBlock(Log(r), v)
                      IN /\ ind <= LogLen(r)
                         /\ Log(r)[ind].view = v

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


AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ LET newCommit == CommitNumber(p) + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ MaxLogEntryInView(Log(r), ViewNumber(p)) >= newCommit
                     \/ r = p
          /\ replicaState' = [replicaState EXCEPT ![p].commitNumber = newCommit]

RecieveCommit(r) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
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

(* View Changing *)

\* -> E1
TimeoutStartViewChanging(r) ==
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
           IN /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = maxReplica,
                                                      \* Will update commit number while downloading
                                                      \* ![p].commitNumber = Max({CommitNumber(r) : r \in recievedReplicas}),
                                                      ![p].status = Normal]

\* Mc -> Mc / Mc -> M
MasterDownloadBeforeView(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ IsDownloadingBeforeView(p)
    /\ ViewNumber(p) = ViewNumber(DownloadReplica(p))  \* If replica will increase view, then this Primary could only start view changing
    /\ LET entriesToDownload == { i \in CommitNumber(p) + 1 .. LogLen(DownloadReplica(p)):
                                  \* New entry for r
                                  \/ LogLen(p) < i
                                  \* Diff in logs
                                  \/ Log(p)[i] # Log(DownloadReplica(p))[i] }
       IN \/ /\ entriesToDownload = {}  \* finish download
             /\ replicaState' = [replicaState EXCEPT ![p].log = Append(@, [type |-> ViewBlock, view |-> ViewNumber(p)]),
                                                     ![p].downloadReplica = None]
          \/ /\ entriesToDownload # {}
             /\ LET ind == Min(entriesToDownload)
                IN /\ replicaState' = [replicaState EXCEPT ![p].log = Append(SubSeq(@, 1, ind - 1), Log(DownloadReplica(p))[ind])]

\* Er -> Rc
\* TODO: setup download up to View metablock
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
    /\ IsDownloadingBeforeView(r)
    /\ LET entriesToDownload == { i \in CommitNumber(r) + 1 .. LogLen(DownloadReplica(r)):
                                  \* New entry for r
                                  \/ LogLen(r) < i
                                  \* Diff in logs
                                  \/ Log(r)[i] # Log(DownloadReplica(r))[i] }
       IN \/ /\ entriesToDownload = {}  \* finish download
             /\ replicaState' = [replicaState EXCEPT ![r].log = Append(@, [type |-> ViewBlock, view |-> ViewNumber(r)]),
                                                     ![r].downloadReplica = None]
          \/ /\ entriesToDownload # {}
             /\ LET ind == Min(entriesToDownload)
                IN /\ replicaState' = [replicaState EXCEPT ![r].log = Append(SubSeq(@, 1, ind - 1), Log(DownloadReplica(r))[ind]),
                                                           ![r].downloadReplica =
                                                               \* Have just downloaded our View meta Block
                                                               IF Log(DownloadReplica(r))[ind] = [type |-> ViewBlock, view |-> ViewNumber(r)] 
                                                               THEN None
                                                               ELSE @]

-----------------------------------------------------------------------------


Next == \/ \E r \in Replica, op \in Operation: RecieveClientRequest(r, op)
        \/ \E r \in Replica: RecievePrepare(r)
        \/ \E p \in Replica: AchievePrepareOkFromQuorum(p)
        \/ \E r \in Replica: RecieveCommit(r)
        \/ \E r \in Replica: TimeoutStartViewChanging(r)
        \/ \E r \in Replica: RecieveStartViewChange(r)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
        \/ \E r \in Replica: RecieveStartView(r)
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
                                                    (IsPrimaryInView(r1, v)
                                                    /\ IsPrimaryInView(r2, v)) => r1 = r2

PreficiesAreEqual(s1, s2) == \A i \in DOMAIN s1 \cap DOMAIN s2: s1[i] = s2[i]

PreficiesOfLenAreEqual(s1, s2, prefLen) == \A i \in DOMAIN s1 \cap DOMAIN s2
                                                              \cap 1..prefLen:
                                                                  s1[i] = s2[i]

CommitedLogsPreficesAreEqual == \A r1, r2 \in Replica: PreficiesOfLenAreEqual(
                                                           Log(r1),
                                                           Log(r2),
                                                           Min({
                                                               CommitNumber(r1),
                                                               CommitNumber(r2)
                                                           })
                                                       )

-----------------------------------------------------------------------------

(* Properties *)

\*AllClientsWillBeServed == \A c \in Client: (pendingRequest[c] ~> ~pendingRequest[c])



-----------------------------------------------------------------------------


=============================================================================
\* Modification History
\* Last modified Wed Apr 26 19:52:06 MSK 2023 by tycoon
\* Created Wed Dec 28 15:30:37 MSK 2022 by tycoon
