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

\* State on each replica
VARIABLE replicaState

VARIABLE msgs

vars == <<replicaState, msgs>>

-----------------------------------------------------------------------------

Statuses == {Normal, ViewChange, Recovering}

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

-----------------------------------------------------------------------------

AddClientRequest(r, m) ==
    /\ replicaState' = [replicaState EXCEPT ![r].log = Append(@, m)]

\* Implemented as Primary "generates" it by itself
RecieveClientRequest(p, op) ==
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
    /\ Status(r) = Normal
    /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                            ![r].viewNumber = @ + 1,
                                            ![r].status = ViewChange]
    /\ Send([type |-> StartViewChange, v |-> ViewNumber(r)', i |-> r])

CheckAchieveStartViewChangeFromQuorum(r, v) ==
    /\ IF \E Q \in Quorum: /\ r \in Q
                           /\ Q = {r} \cup {m.i : m \in {m \in msgs: m.type = StartViewChange /\ m.v = replicaState'[r].viewNumber}}
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
          /\ UNCHANGED <<replicaState>>
          /\ CheckAchieveStartViewChangeFromQuorum(r, m.v)
       \/ \* Stale view
          /\ \/ ViewNumber(r) > m.v
             \/ /\ ViewNumber(r) = m.v
                /\ Status(r) = Normal
          /\ UNCHANGED <<replicaState, msgs>>

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
                 maxReplica == (CHOOSE m \in recieved: ReplicaIndex(m.i) = maxReplicaIndex).i
             IN /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = maxReplica,
                                                        ![p].status = Normal]
                /\ Send([type |-> StartDownload, v |-> ViewNumber(p), n |-> CommitNumber(p) + 1, src |-> maxReplica])

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

(*
\* Mc / Rc
ReceiveDownloadChunk(r) ==
    /\ Status(r) # Recovering
    /\ IsDownloading(r)
    /\ LET msgsToDownload == { msg \in msgs:
                                   /\ msg.type = DownloadChunk 
                                   /\ msg.v = ViewNumber(r)
                                   /\ msg.i = DownloadReplica(r)
                                   /\ \/ LogLen(r) + 1 = msg.n
                                      \/ /\ LogLen(r) >= msg.n
                                         /\ Log(r)[msg.n] # msg.m }
       IN /\ msgsToDownload # {}
          /\ LET MinOpNum == Min({msg.n: msg \in msgsToDownload})
                 MinMsg == CHOOSE msg \in msgsToDownload: msg.n = MinOpNum
             IN /\ replicaState' = [replicaState EXCEPT ![r].log = Append(SubSeq(@, 1, MinOpNum - 1), MinMsg.m),
                                                        ![r].commitNumber = MinMsg.k]
                /\ UNCHANGED <<msgs>>
*)

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
          /\ LET doViewChangeReceived == {m \in msgs: m.type = DoViewChange /\ m.v = ViewNumber(p) /\ m.i = DownloadReplica(p)}
                 finished == OpNumber(p) + 1 >= (CHOOSE m \in doViewChangeReceived: TRUE).n
                 MinOpNum == Min({msg.n: msg \in msgsToDownload})
                 MinMsg == CHOOSE msg \in msgsToDownload: msg.n = MinOpNum
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
    /\ LET msgsToDownload == { msg \in msgs:
                                   /\ msg.type = DownloadChunk 
                                   /\ msg.v = ViewNumber(r)
                                   /\ msg.i = DownloadReplica(r)
                                   /\ \/ LogLen(r) + 1 = msg.n
                                      \/ /\ LogLen(r) >= msg.n
                                         /\ Log(r)[msg.n] # msg.m }
       IN /\ msgsToDownload # {}
          /\ LET MinOpNum == Min({msg.n: msg \in msgsToDownload})
                 MinMsg == CHOOSE msg \in msgsToDownload: msg.n = MinOpNum
                 finished == MinMsg.m = [type |-> ViewBlock, view |-> ViewNumber(r)]
             IN /\ replicaState' = [replicaState EXCEPT ![r].log = Append(SubSeq(@, 1, MinOpNum - 1), MinMsg.m),
                                                        ![r].downloadReplica =
                                                             IF finished
                                                             THEN None
                                                             ELSE @]
    /\ UNCHANGED <<msgs>>

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
\*    \/ \E r \in Replica: ReceiveDownloadChunk(r)
    \/ \E p \in Replica: MasterDownloadBeforeView(p)
    \/ \E r \in Replica, m \in msgs: RecieveStartView(r, m)
    \/ \E r \in Replica: ReplicaDownloadBeforeView(r)

Next == \/ NormalOperationProtocol
        \/ ViewChangeProtocol

-----------------------------------------------------------------------------

(* Liveness *)

EventuallyRecieveClientRequest == \A r \in Replica: WF_vars(\E op \in Operation: RecieveClientRequest(r, op))

EventuallyRecievePrepare == \A r \in Replica: WF_vars(\E m \in msgs: RecievePrepare(r, m))

EventuallyRecieveCommit == \A r \in Replica: WF_vars(\E m \in msgs: RecieveCommit(r, m))

LivenessSpec ==
    /\ EventuallyRecieveClientRequest
    /\ EventuallyRecievePrepare
    /\ EventuallyRecieveCommit

-----------------------------------------------------------------------------

(* Full Spec *)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

VRNoMsgs == INSTANCE VR_without_message

-----------------------------------------------------------------------------

(* INVARIANTS *)

EveryViewHasAtLeastOnePrimary == \A v \in 0..10: \E r \in Replica: IsPrimaryInView(r, v)

EveryViewHasAtMostOnePrimary == \A v \in 0..10: \A r1, r2 \in Replica:
                                                    (IsPrimaryInView(r1, v) /\ IsPrimaryInView(r2, v)) => r1 = r2

PreficiesAreEqual(s1, s2) == \A i \in DOMAIN s1 \cap DOMAIN s2: s1[i] = s2[i]

PreficiesOfLenAreEqual(s1, s2, prefLen) == \A i \in DOMAIN s1 \cap DOMAIN s2 \cap 1..prefLen: s1[i] = s2[i]

CommitedLogsPreficesAreEqual == \A r1, r2 \in Replica: PreficiesOfLenAreEqual(Log(r1), Log(r2), Min({CommitNumber(r1), CommitNumber(r2)}))

-----------------------------------------------------------------------------

(* Properties *)

\*AllClientsWillBeServed == \A c \in Client: (pendingRequest[c] ~> ~pendingRequest[c])

-----------------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Thu May 04 22:56:11 MSK 2023 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
