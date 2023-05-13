----------------------- MODULE ViewstampedReplication -----------------------
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

\* Message types for processing logs
CONSTANTS DownloadChunk, StartDownload, PrepareOk, Commit

\* Message types for view changing
CONSTANTS StartViewChange, DoViewChange, StartView

\* Sequence with all replicas (for view selection)
CONSTANT ReplicaSequence

\* For state space limitation
CONSTANT MaxRequests, MaxViews

\* State on each replica
VARIABLE replicaState

VARIABLE msgs

vars == <<replicaState, msgs>>

-----------------------------------------------------------------------------

LogEntry == [type: {RequestBlock}, opNumber: Nat, op: Operation]
       \cup [type: {ViewBlock}, view: Nat]

\* All possible messages
Message == [type: {DownloadChunk}, v: Nat, m: LogEntry, n: Nat, k: Nat, i: Replica]
      \cup [type: {StartDownload}, v: Nat, n: Nat, src: Replica]
      \cup [type: {PrepareOk}, v: Nat, n: Nat, i: Replica]
      \cup [type: {Commit}, v: Nat, k: Nat]
      \cup [type: {StartViewChange}, v: Nat, i: Replica]
      \cup [type: {DoViewChange}, v: Nat, vv: Nat,
            n: Nat, k: Nat, i: Replica]
      \cup [type: {StartView}, v: Nat, n: Nat, k: Nat]

Send(m) == msgs' = msgs \cup {m}

SendAll(ms) == /\ msgs' = msgs \cup ms

Statuses == {Normal, ViewChange, Recovering}

TypeOK == /\ replicaState \in [
            Replica -> [
                viewNumber: Nat,
                status: Statuses,
                log: Seq(LogEntry),
                downloadReplica: Replica \cup {None},
                commitNumber: Nat
              ]
            ]
          /\ msgs \in SUBSET Message

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Replica
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

ASSUME IsFiniteSet(Replica)

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

Min(S) == CHOOSE x \in S: \A y \in S: x <= y

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
        /\ msgs = {}

-----------------------------------------------------------------------------

\* Getters

ViewNumber(r) == replicaState[r].viewNumber

Status(r) == replicaState[r].status

Log(r) == replicaState[r].log

LogLen(r) == Len(Log(r))

LastNormalView(r) == Max({Log(r)[v].view : v \in {i \in 1 .. LogLen(r) : Log(r)[i].type = ViewBlock}})

OpNumber(r) == LogLen(r)

DownloadReplica(r) == replicaState[r].downloadReplica

CommitNumber(r) == replicaState[r].commitNumber

\* Helpful functions

ReplicaIndex(r) == CHOOSE i \in 1..Cardinality(Replica): ReplicaSequence[i] = r

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, ViewNumber(r))

IsDownloading(r) ==
    /\ replicaState[r].downloadReplica # None

RequestBlockCount(log) == Cardinality({i \in DOMAIN log: log[i].type = RequestBlock})

ViewBlockCount(log) == Cardinality({i \in DOMAIN log: log[i].type = ViewBlock})

-----------------------------------------------------------------------------

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
    /\ Send([type |-> DownloadChunk,
             v |-> ViewNumber(p), m |-> Log(p)'[OpNumber(p) + 1],
             n |-> OpNumber(p) + 1, k |-> CommitNumber(p), i |-> p])

RecievePrepare(r, m) ==
    /\ RequestBlockCount(Log(r)) < MaxRequests
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloading(r)
    /\ m.type = DownloadChunk
    /\ m.v = ViewNumber(r)
    /\ m.n = OpNumber(r) + 1
    /\ m.i = PrimaryReplicaInView(ViewNumber(r))
    /\ AddClientRequest(r, m.m)
    /\ Send([type |-> PrepareOk,
             v |-> ViewNumber(r), n |-> m.n, i |-> r])

PrepareOperation(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloading(r)
    /\ LET maxPreparedOpNum == Max({0} \cup {m.n : m \in {m \in msgs: m.type = PrepareOk /\ m.i = r /\ m.v = ViewNumber(r)}})
       IN /\ LogLen(r) > maxPreparedOpNum
          /\ Send([type |-> PrepareOk, v |-> ViewNumber(r),
                   n |-> maxPreparedOpNum + 1, i |-> r])
    /\ UNCHANGED <<replicaState>>

AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloading(p)
    /\ LET newCommit == CommitNumber(p) + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ Q \subseteq {r} \cup {m.i : m \in {m \in msgs: m.type = PrepareOk /\ m.v = ViewNumber(p) /\ m.n >= newCommit}}
                     \/ r = p
          /\ replicaState' = [replicaState EXCEPT ![p].commitNumber = newCommit]
          /\ Send([type |-> Commit, v |-> ViewNumber(p), k |-> replicaState[p].commitNumber'])

RecieveCommit(r, m) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloading(r)
    /\ m.type = Commit
    /\ m.v = ViewNumber(r)
    /\ m.k > CommitNumber(r)
    /\ replicaState' = [replicaState EXCEPT ![r].commitNumber = m.k] 
    /\ UNCHANGED <<msgs>>

-----------------------------------------------------------------------------

(* View Changing *)

TimeoutStartViewChanging(r) ==
    /\ ViewNumber(r) + 1 < MaxViews
    /\ Status(r) = Normal
    /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                            ![r].viewNumber = @ + 1,
                                            ![r].status = ViewChange]
    /\ Send([type |-> StartViewChange, v |-> ViewNumber(r)', i |-> r])

CheckAchieveStartViewChangeFromQuorum(r, v) ==
    /\ IF \E Q \in Quorum: /\ r \in Q
                           /\ Q = {r} \cup {m.i : m \in {m \in msgs: m.type = StartViewChange
                                                         /\ m.v = replicaState'[r].viewNumber}}
       THEN Send([type |-> DoViewChange, v |-> v, vv |-> LastNormalView(r),
                  n |-> OpNumber(r), k |-> CommitNumber(r), i |-> r])
       ELSE UNCHANGED <<msgs>>

RecieveStartViewChange(r, m) ==
    /\ m.type = StartViewChange
    /\ \/ \* Start View Changing
          /\ ViewNumber(r) < m.v
          /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                                  ![r].viewNumber = m.v,
                                                  ![r].status = ViewChange]
          /\ CheckAchieveStartViewChangeFromQuorum(r, m.v)
       \/ \* Our view number
          /\ ViewNumber(r) = m.v
          /\ Status(r) = ViewChange
          /\ \E Q \in Quorum: /\ r \in Q
                              /\ Q = {r} \cup {m.i : mm \in {mm \in msgs: mm.type = StartViewChange
                                                             /\ mm.v = m.v}}
          /\ Send([type |-> DoViewChange, v |-> m.v, vv |-> LastNormalView(r),
                   n |-> OpNumber(r), k |-> CommitNumber(r), i |-> r])
          /\ UNCHANGED <<replicaState>>

RecieveDoViewChange(p, m) ==
    /\ m.type = DoViewChange
    /\ IsPrimaryInView(p, m.v)
    /\ ViewNumber(p) < m.v
    /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = None,
                                            ![p].viewNumber = m.v,
                                            ![p].status = ViewChange]
    /\ UNCHANGED <<msgs>>

\* Become Primary
AchieveDoViewChangeFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = ViewChange
    /\ LET recieved == {m \in msgs: m.type = DoViewChange /\ m.v = ViewNumber(p)} \cup
                           {[type |-> DoViewChange, v |-> ViewNumber(p), vv |-> LastNormalView(p),
                             n |-> OpNumber(p), k |-> CommitNumber(p), i |-> p]}
       IN /\ \E Q \in Quorum: /\ p \in Q
                              /\ Q \subseteq {m.i : m \in recieved}
                  
          /\ LET maxVV == Max({m.vv : m \in recieved})
                 maxN == Max({m.n : m \in {m \in recieved : m.vv = maxVV}})
                 maxReplicaIndex == Max({ReplicaIndex(m.i) : m \in {m \in recieved : m.vv = maxVV /\ m.n = maxN}})
                 maxReplica == IF /\ maxVV = LastNormalView(p)
                                  /\ maxN = OpNumber(p)
                               THEN p
                               ELSE (CHOOSE m \in recieved: ReplicaIndex(m.i) = maxReplicaIndex).i
             IN /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = IF maxReplica = p
                                                                               THEN None
                                                                               ELSE maxReplica,
                                                        ![p].log = IF maxReplica = p
                                                                   THEN Append(@, [type |-> ViewBlock, view |-> ViewNumber(p)])
                                                                   ELSE @,
                                                        ![p].status = Normal]
                /\ IF maxReplica = p
                   THEN Send([type |-> StartView, v |-> ViewNumber(p), n |-> OpNumber(p)', k |-> replicaState[p].commitNumber'])
                   ELSE Send([type |-> StartDownload, v |-> ViewNumber(p), n |-> CommitNumber(p) + 1, src |-> maxReplica])

SendDownloadChunks(r) ==
    /\ Status(r) # Recovering
    /\ \E m \in msgs:
           /\ m.type = StartDownload
           /\ m.src = r
           /\ m.v = ViewNumber(r)
           /\ SendAll({ [type |-> DownloadChunk,
                         v |-> ViewNumber(r), m |-> Log(r)[opNum],
                         n |-> opNum, k |-> CommitNumber(r), i |-> r]: opNum \in m.n .. LogLen(r) })
           /\ UNCHANGED <<replicaState>>

\* Mc -> Mc / Mc -> M
MasterDownloadBeforeView(p) ==
    /\ IsPrimary(p)
    /\ Status(p) # Recovering
    /\ IsDownloading(p)
    /\ LET msgsToDownload == { msg \in msgs:
                                   /\ msg.type = DownloadChunk 
                                   /\ msg.v = ViewNumber(p)
                                   /\ msg.i = DownloadReplica(p)
                                   /\ \/ LogLen(p) + 1 = msg.n
                                      \/ /\ LogLen(p) >= msg.n
                                         /\ Log(p)[msg.n] # msg.m }
       IN /\ msgsToDownload # {}
          /\ LET doViewChangeReceived == {m \in msgs: m.type = DoViewChange /\ m.v = ViewNumber(p)}
                 MinOpNum == Min({msg.n: msg \in msgsToDownload})
                 MinMsg == CHOOSE msg \in msgsToDownload: msg.n = MinOpNum
                 finished == MinOpNum >= (CHOOSE m \in doViewChangeReceived: m.i = DownloadReplica(p)).n
                 IN /\ replicaState' = [replicaState EXCEPT ![p].log =
                                                                 IF finished
                                                                 THEN Append(
                                                                          Append(SubSeq(@, 1, MinOpNum - 1), MinMsg.m),
                                                                          [type |-> ViewBlock, view |-> ViewNumber(p)]
                                                                      )
                                                                 ELSE Append(SubSeq(@, 1, MinOpNum - 1), MinMsg.m),
                                                            ![p].downloadReplica =
                                                                 IF finished
                                                                 THEN None
                                                                 ELSE @]
                    /\ IF finished
                       THEN Send([type |-> StartView,
                                  v |-> ViewNumber(p),
                                  n |-> OpNumber(p)',
                                  k |-> replicaState[p].commitNumber'])
                       ELSE UNCHANGED <<msgs>>

RecieveStartView(r, m) ==
    /\ m.type = StartView
    /\ \/ ViewNumber(r) < m.v
       \/ /\ ViewNumber(r) = m.v
          /\ Status(r) = ViewChange
    /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = PrimaryReplicaInView(m.v),
                                            ![r].viewNumber = m.v,
                                            ![r].status = Normal]
    /\ Send([type |-> StartDownload, v |-> m.v, n |-> CommitNumber(r) + 1, src |-> PrimaryReplicaInView(m.v)])

\* Rc -> Rc / Rc -> R
ReplicaDownloadBeforeView(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ IsDownloading(r)
    /\ LET allMsgsToDownload == { msg \in msgs:
                                   /\ msg.type = DownloadChunk
                                   /\ msg.v = ViewNumber(r)
                                   /\ msg.n > CommitNumber(r)
                                   /\ msg.i = DownloadReplica(r) }
           msgsToDownload == { msg \in allMsgsToDownload:
                                   \/ LogLen(r) + 1 = msg.n
                                   \/ /\ LogLen(r) >= msg.n
                                      /\ Log(r)[msg.n] # msg.m}
       IN /\ msgsToDownload # {}
          /\ LET MinOpNum == Min({msg.n: msg \in msgsToDownload})
                 MinMsg == CHOOSE msg \in msgsToDownload: msg.n = MinOpNum
                 finished == MinMsg.m = [type |-> ViewBlock, view |-> ViewNumber(r)]
             IN /\ \* all previous chunks are exist (or else it is another download)
                   \A prevPos \in CommitNumber(r) + 1 .. MinMsg.n - 1:
                       \E prev \in allMsgsToDownload:
                           /\ prev.type = DownloadChunk
                           /\ prev.v = ViewNumber(r)
                           /\ prev.i = DownloadReplica(r)
                           /\ prev.n = prevPos
                /\ replicaState' = [replicaState EXCEPT ![r].log = Append(SubSeq(@, 1, MinOpNum - 1), MinMsg.m),
                                                        ![r].downloadReplica =
                                                             IF finished
                                                             THEN None
                                                             ELSE @]
    /\ UNCHANGED <<msgs>>

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
    /\ UNCHANGED <<replicaState, msgs>>

-----------------------------------------------------------------------------

NormalOperationProtocol ==
    \/ \E r \in Replica, op \in Operation: RecieveClientRequest(r, op)
    \/ \E r \in Replica, m \in msgs: RecievePrepare(r, m)
    \/ \E r \in Replica: PrepareOperation(r)
    \/ \E p \in Replica: AchievePrepareOkFromQuorum(p)
    \/ \E r \in Replica, m \in msgs: RecieveCommit(r, m)
        
ViewChangeProtocol ==
    \/ \E r \in Replica: TimeoutStartViewChanging(r)
    \/ \E r \in Replica, m \in msgs: RecieveStartViewChange(r, m)
    \/ \E p \in Replica, m \in msgs: RecieveDoViewChange(p, m)
    \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
    \/ \E r \in Replica: SendDownloadChunks(r)
    \/ \E p \in Replica: MasterDownloadBeforeView(p)
    \/ \E r \in Replica, m \in msgs: RecieveStartView(r, m)
    \/ \E r \in Replica: ReplicaDownloadBeforeView(r)

Next == \/ NormalOperationProtocol
        \/ ViewChangeProtocol
        \/ Finishing

-----------------------------------------------------------------------------

(* Full Spec *)

Spec == Init /\ [][Next]_vars

FullSpec == /\ Init
            /\ [][Next]_vars
            /\ WF_<<vars>>(\E r \in Replica, m \in msgs: RecieveStartViewChange(r, m))
            /\ WF_<<vars>>(\E r \in Replica, op \in Operation: RecieveClientRequest(r, op))
            /\ WF_<<vars>>(\E r \in Replica, m \in msgs: RecievePrepare(r, m))
            /\ WF_<<vars>>(\E r \in Replica: PrepareOperation(r))
            /\ WF_<<vars>>(\E p \in Replica: AchievePrepareOkFromQuorum(p))
            /\ WF_<<vars>>(\E r \in Replica, m \in msgs: RecieveCommit(r, m))
            /\ WF_<<vars>>(\E r \in Replica: TimeoutStartViewChanging(r))
            /\ WF_<<vars>>(\E r \in Replica, m \in msgs: RecieveStartViewChange(r, m))
            /\ WF_<<vars>>(\E p \in Replica, m \in msgs: RecieveDoViewChange(p, m))
            /\ WF_<<vars>>(\E r \in Replica: AchieveDoViewChangeFromQuorum(r))
            /\ WF_<<vars>>(\E r \in Replica: SendDownloadChunks(r))
            /\ WF_<<vars>>(\E p \in Replica: MasterDownloadBeforeView(p))
            /\ WF_<<vars>>(\E r \in Replica, m \in msgs: RecieveStartView(r, m))
            /\ WF_<<vars>>(\E r \in Replica: ReplicaDownloadBeforeView(r))

-----------------------------------------------------------------------------

VRNoMsgs == INSTANCE VR_without_message

THEOREM Spec => VRNoMsgs!Spec

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
\* Last modified Fri May 12 14:50:50 MSK 2023 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
