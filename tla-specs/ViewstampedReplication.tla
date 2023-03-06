----------------------- MODULE ViewstampedReplication -----------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Replica, Quorum

\* Replica Status
CONSTANTS Normal, ViewChange, Recovering

Statuses == {Normal, ViewChange, Recovering}

\* Client operation
CONSTANT Operation

\* Result of executing operation
Result == Operation

\* types of log blocks
CONSTANTS RequestBlock, ViewBlock

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

(*
\* State on each replica
VARIABLES viewNumber, status, lastNormalView,
          opNumber, log, commitNumber, prepared,
          executedOperations
*)

\* State on each replica
VARIABLE replicaState

\* Persistant state on each replica
VARIABLE recoveryCount

VARIABLE msgs

(*
\* State on Primary replica
VARIABLES (*sentPreparedOpNumber, *)recievedPrepareOkOpNumber(*, sentCommitNumber, sentStartView*)

\* State on View Changing replica
VARIABLES (*sentStartViewChange, *)recievedStartViewChange, recievedDoViewChangeMsgs
*)

(*
replicaViewVars == <<viewNumber, status, lastNormalView>>

replicaViewChangeVars == <<(*sentStartViewChange, *)recievedStartViewChange, recievedDoViewChangeMsgs>>

replicaLogVars == <<opNumber, log>>

replicaExecVars == <<commitNumber, prepared, executedOperations>>

primaryVars == <<(*sentPreparedOpNumber, *)recievedPrepareOkOpNumber(*, sentCommitNumber, sentStartView*)>>

replicaStateVars == <<replicaViewVars, replicaViewChangeVars, replicaLogVars, replicaExecVars, primaryVars>>
*)
vars == <<replicaState, msgs, recoveryCount>>

-----------------------------------------------------------------------------

RequestMessage == [type: {Request}, op: Operation]

LogEntry == [type: {RequestBlock}, opNumber: Nat, m: RequestMessage]
       \cup [type: {ViewBlock}, view: Nat]

\* All possible messages
Message == [type: {Prepare}, v: Nat, m: RequestMessage, n: Nat, k: Nat]
      \cup [type: {PrepareOk}, v: Nat, n: Nat, i: Replica]
      \cup [type: {Commit}, v: Nat, k: Nat]
      \cup [type: {StartViewChange}, v: Nat, i: Replica]
      \cup [type: {DoViewChange}, v: Nat, vv: Nat,
            n: Nat, k: Nat, i: Replica]
      \cup [type: {StartView}, v: Nat, n: Nat, k: Nat]
      \cup [type: {Recovery}, i: Replica, x: Nat]
      \cup [type: {RecoveryResponse}, v: Nat, x: Nat, l: Seq(LogEntry) \cup {None},
            n: Nat \cup {None}, k: Nat \cup {None}, i: Replica, j: Replica]

\* TODO: add losing, dublicating, out of order messages
Send(m) == msgs' = msgs \cup {m}

Drop(m) == 
    /\ msgs' = msgs \ {m}

ReplyMessage(request, response) ==
    /\ request \in msgs
    /\ msgs' = (msgs \ {request}) \cup {response}

TypeOK == /\ recoveryCount \in [Replica -> Nat]
          /\ replicaState \in [
            Replica -> [
                viewNumber: Nat,
                status: Statuses,
                lastNormalView: Nat,
                log: Seq(LogEntry),
                downloadReplica: Replica \cup {None},
                commitNumber: Nat,
                executedOperations: Seq(LogEntry)
              ]
            ]
          /\ recoveryCount \in [Replica -> Nat]
          /\ msgs \in SUBSET Message
          (*/\ viewNumber \in [Replica -> View]
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
\*          /\ sentStartView \in [Replica -> SUBSET Replica]*)

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
                    lastNormalView |-> 0,
                    log |-> << [type |-> ViewBlock, view |-> 0] >>,
                    downloadReplica |-> None,
                    commitNumber |-> 0,
                    executedOperations |-> << >>
                ]
           ]
        /\ recoveryCount = [r \in Replica |-> 0]
        /\ msgs = {}

-----------------------------------------------------------------------------

\* Getters

ViewNumber(r) == replicaState[r].viewNumber

Status(r) == replicaState[r].status

LastNormalView(r) == replicaState[r].lastNormalView 

Log(r) == replicaState[r].log

LogLen(r) == Len(Log(r))

OpNumber(r) == LogLen(r)

NewOpNumber(r) == Len(Log(r)')

DownloadReplica(r) == replicaState[r].downloadReplica

CommitNumber(r) == replicaState[r].commitNumber

ExecutedOperations(r) == replicaState[r].executedOperations

RecievedPrepareOkOpNumber(r) == replicaState[r].recievedPrepareOkOpNumber

\* Helpful functions

ExecuteOperation(op) == op

PrimaryReplicaInView(v) == ReplicaSequence[(v % Len(ReplicaSequence)) + 1]

IsPrimaryInView(r, v) == PrimaryReplicaInView(v) = r

IsPrimary(r) == IsPrimaryInView(r, ViewNumber(r))

IsDownloadingBeforeView(r) ==
    /\ replicaState[r].downloadReplica # None

AddClientRequest(r, m) ==
    /\ replicaState' = [replicaState EXCEPT ![r].log = Append(@, [
                                                type |-> RequestBlock,
                                                opNumber |-> OpNumber(r) + 1,
                                                m |-> m
                                              ])]

\* Implemented as Primary "generates" it by itself
RecieveClientRequest(p, op) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ AddClientRequest(p, [type |-> Request, op |-> op])
    /\ Send([type |-> Prepare,
             v |-> ViewNumber(p), m |-> Log(p)'[OpNumber(p) + 1].m,
             n |-> OpNumber(p) + 1, k |-> CommitNumber(p)])
    /\ UNCHANGED <<recoveryCount>>

RecievePrepare(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ m.type = Prepare
    /\ m.v = ViewNumber(r)
    /\ m.n = OpNumber(r) + 1
    /\ AddClientRequest(r, m.m)
    /\ Send([(*src |-> r, dst |-> PrimaryReplicaInView(viewNumber[r]), *)type |-> PrepareOk,
             v |-> ViewNumber(r), n |-> m.n, i |-> r])
    /\ UNCHANGED <<recoveryCount>>

PrepareOperation(r) ==
    /\ ~IsPrimary(r)
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ LET maxPreparedOpNum == Max({0} \cup {m.n : m \in {m \in msgs: m.type = PrepareOk /\ m.i = r /\ m.v = ViewNumber(r)}})
       IN /\ LogLen(r) > maxPreparedOpNum
          /\ Send([type |-> PrepareOk, v |-> ViewNumber(r),
                   n |-> maxPreparedOpNum + 1, i |-> r])
    /\ UNCHANGED <<recoveryCount, replicaState>>

ExecuteRequest(r, entry) ==
    /\ replicaState' = [replicaState EXCEPT ![r].executedOperations = Append(@, entry)]

ExecuteClientRequest(r) ==
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ Len(ExecutedOperations(r)) < CommitNumber(r)
    /\ Len(ExecutedOperations(r)) < LogLen(r)
    /\ ExecuteRequest(r, Log(r)[Len(ExecutedOperations(r)) + 1])
    /\ UNCHANGED <<recoveryCount, msgs>>

AchievePrepareOkFromQuorum(p) ==
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ Len(ExecutedOperations(p)) = CommitNumber(p)
    /\ LET newCommit == CommitNumber(p) + 1
       IN /\ \E Q \in Quorum:
                 \A r \in Q:
                     \/ Q \subseteq {r} \cup {m.i : m \in {m \in msgs: m.type = PrepareOk /\ m.v = ViewNumber(p) /\ m.n >= newCommit}}
                     \/ r = p
          /\ replicaState' = [replicaState EXCEPT ![p].commitNumber = newCommit,
                                                  ![p].executedOperations = Append(@, Log(p)[newCommit])]  \* ExecuteRequest(p, Log(p)[newCommit])
          /\ Send([type |-> Commit, v |-> ViewNumber(p), k |-> replicaState[p].commitNumber'])
    /\ UNCHANGED <<recoveryCount>>

\* TODO
(*
RecievePrepareOk(p, m) ==
    /\ m.type = PrepareOk
    /\ p # m.i
    /\ IsPrimary(p)
    /\ Status(p) = Normal
    /\ ~IsDownloadingBeforeView(p)
    /\ \/ \* stale prepareOkMessage
          /\ m.n <= RecievedPrepareOkOpNumber(p)[m.i]
          /\ Drop(m)
          /\ UNCHANGED <<replicaState>>
       \/ \*
          /\ m.n > RecievedPrepareOkOpNumber(p)[m.i]
          /\ replicaState' = [replicaState EXCEPT ![p].recievedPrepareOkOpNumber[m.i] = m.n]  \* in NoMsg just +1
          /\ UNCHANGED <<msgs>>
    /\ UNCHANGED <<recoveryCount>>
*)

RecieveCommit(r, m) ==
    /\ ~IsPrimary(r)  \* Need this?
    /\ Status(r) = Normal
    /\ ~IsDownloadingBeforeView(r)
    /\ m.type = Commit
    /\ m.k > CommitNumber(r)
    /\ replicaState' = [replicaState EXCEPT ![r].commitNumber = m.k] 
    /\ UNCHANGED <<recoveryCount, msgs>>

-----------------------------------------------------------------------------

(* View Changing *)

TimeoutStartViewChanging(r) ==
    /\ Status(r) = Normal
    /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                            ![r].viewNumber = @ + 1,
                                            ![r].status = ViewChange]
    /\ Send([type |-> StartViewChange, v |-> replicaState[r].viewNumber', i |-> r])
    /\ UNCHANGED <<recoveryCount>>

CheckAchieveStartViewChangeFromQuorum(r, v) ==
    /\ IF \E Q \in Quorum: /\ r \in Q
                           /\ Q = {r} \cup {m.i : m \in {m \in msgs: m.type = StartViewChange /\ m.v = ViewNumber(r)'}}
       THEN Send([(*src |-> r, dst |-> PrimaryReplicaInView(m.v),*)
                  type |-> DoViewChange, v |-> v, vv |-> LastNormalView(r),
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
          /\ replicaState' = [replicaState EXCEPT ![r].downloadReplica = None,
                                                  ![r].viewNumber = m.v,
                                                  ![r].status = ViewChange]
          /\ CheckAchieveStartViewChangeFromQuorum(r, m.v)
       \/ \* Stale view
          /\ \/ ViewNumber(r) > m.v
             \/ /\ ViewNumber(r) = m.v
                /\ Status(r) = Normal
          /\ UNCHANGED <<replicaState, msgs>>
    /\ UNCHANGED <<recoveryCount>>

RecieveDoViewChange(p, m) ==
    /\ m.type = DoViewChange
    /\ IsPrimaryInView(p, m.v)
    /\ \/ \* Update view number
          /\ ViewNumber(p) < m.v
          /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = None,
                                                  ![p].viewNumber = m.v,
                                                  ![p].status = ViewChange]
       \/ \* Our view number or Stale message
          /\ UNCHANGED <<replicaState>>
    /\ Drop(m)
    /\ UNCHANGED <<recoveryCount>>

\* Become Primary
AchieveDoViewChangeFromQuorum(p) ==
    /\ Status(p) = ViewChange
    /\ IsPrimaryInView(p, ViewNumber(p))
    /\ LET recieved == {m \in msgs: m.type = DoViewChange /\ m.v = ViewNumber(p)}
       IN /\ \E Q \in Quorum: /\ p \in Q
                              /\ Q \subseteq {p} \cup {m.i : m \in recieved}
          /\ LET maxVV == Max({m.vv : m \in recieved})
                 maxN == Max({m.n : m \in {m \in recieved : m.vv = maxVV}})
                 maxMsg == CHOOSE m \in recieved: m.vv = maxVV /\ m.n = maxN
                 newLog == maxMsg.l
             IN /\ replicaState' = [replicaState EXCEPT ![p].downloadReplica = maxMsg.i,
                                                        ![p].commitNumber = Max({m.k : m \in recieved}),
                                                        ![p].status = Normal,
                                                        ![p].lastNormalView = ViewNumber(p)]
    /\ UNCHANGED <<recoveryCount, msgs>>

\* TODO: add messages for downloading
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
                                                     ![p].downloadReplica = None]
             /\ Send([type |-> StartView,
                      v |-> ViewNumber(p),
                      n |-> OpNumber(p)',
                      k |-> replicaState[p].commitNumber'])
          \/ /\ replicaState' = [replicaState EXCEPT ![p].log = Append(@, newEntry)]
             /\ UNCHANGED <<msgs>>
    /\ UNCHANGED <<recoveryCount>>

RecieveStartView(r, m) ==
    /\ m.type = StartView
    /\ \/ ViewNumber(r) < m.v
       \/ /\ ViewNumber(r) = m.v
          /\ Status(r) = ViewChange
    /\ replicaState' = [replicaState EXCEPT ![r].log = SubSeq(Log(r), 1, Min({LogLen(r), m.k})),
                                            ![r].downloadReplica = PrimaryReplicaInView(m.v),
                                            ![r].viewNumber = m.v,
                                            ![r].status = Normal,
                                            ![r].lastNormalView = ViewNumber(r),
                                            ![r].commitNumber = m.k]
    /\ UNCHANGED <<recoveryCount, msgs>>

\* TODO: add messages for downloading
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
    /\ UNCHANGED <<recoveryCount, msgs>>

-----------------------------------------------------------------------------

(* Recovery *)

ReplicaCrash(r) ==
    /\ replicaState' = [replicaState EXCEPT ![r].status = Recovering,
                                            ![r].viewNumber = 0,
                                            ![r].lastNormalView = 0,
                                            ![r].log = << >>,
                                            ![r].commitNumber = 0,
                                            ![r].executedOperations = << >>,
                                            ![r].downloadReplica = None]
    /\ recoveryCount' = [recoveryCount EXCEPT ![r] = recoveryCount[r] + 1]
    /\ Send([type |-> Recovery, i |-> r, x |-> recoveryCount'[r]])

RecoveryReceive(r, m) ==
    /\ Status(r) = Normal
    /\ m.type = Recovery
    /\ IF IsPrimary(r)
       THEN /\ Send([type |-> RecoveryResponse, v |-> ViewNumber(r), x |-> m.x,
                     l |-> Log(r), n |-> OpNumber(r), k |-> CommitNumber(r), i |-> m.i, j |-> r])
       ELSE /\ Send([type |-> RecoveryResponse, v |-> ViewNumber(r), x |-> m.x,
                     l |-> None, n |-> None, k |-> None, i |-> m.i, j |-> r])
    /\ UNCHANGED <<replicaState, recoveryCount>>

AchieveRecoveryResponseFromQuorum(r) ==
    /\ Status(r) = Recovering
    /\ \E Q \in Quorum:
           LET recRespMsgs == {m \in msgs: m.type = RecoveryResponse /\ m.i = r /\ m.x = recoveryCount[r]}
               maxView == Max({m.v: m \in recRespMsgs})
               newLog == CHOOSE l \in {m.l: m \in recRespMsgs}: l # None
               newOpNumber == CHOOSE n \in {m.n: m \in recRespMsgs}: n # None
               newCommitNumber == CHOOSE k \in {m.k: m \in recRespMsgs}: k # None
           IN /\ Q = {m.j: m \in recRespMsgs}
              /\ \E p \in Q: IsPrimaryInView(p, maxView)
              /\ replicaState' = [replicaState EXCEPT ![r].status = Normal,
                                                      ![r].viewNumber = maxView,
                                                      ![r].log = newLog,
                                                      ![r].lastNormalView = maxView,
                                                      ![r].commitNumber = newCommitNumber]
              /\ UNCHANGED <<recoveryCount, msgs>>

-----------------------------------------------------------------------------


Next == \/ \E r \in Replica, op \in Operation: RecieveClientRequest(r, op)
        \/ \E r \in Replica, m \in msgs: RecievePrepare(r, m)
        \/ \E r \in Replica: PrepareOperation(r)
        \/ \E p \in Replica: AchievePrepareOkFromQuorum(p)
        \/ \E r \in Replica, m \in msgs: RecieveCommit(r, m)
        \/ \E r \in Replica: ExecuteClientRequest(r)
(*
        \/ \E r \in Replica: TimeoutStartViewChanging(r)
        \/ \E r \in Replica, m \in msgs: RecieveStartViewChange(r, m)
        \/ \E p \in Replica, m \in msgs: RecieveDoViewChange(p, m)
        \/ \E r \in Replica: AchieveDoViewChangeFromQuorum(r)
        \/ \E p \in Replica: MasterDownloadBeforeView(p)
        \/ \E r \in Replica, m \in msgs: RecieveStartView(r, m)
        \/ \E r \in Replica: ReplicaDownloadBeforeView(r)
        \/ \E r \in Replica: ReplicaCrash(r)
        \/ \E r \in Replica, m \in msgs: RecoveryReceive(r, m)
        \/ \E r \in Replica: AchieveRecoveryResponseFromQuorum(r)
*)
-----------------------------------------------------------------------------

(* Liveness *)

EventuallyRecieveClientRequest == \A r \in Replica: WF_vars(\E op \in Operation: RecieveClientRequest(r, op))

EventuallyRecievePrepare == \A r \in Replica: WF_vars(\E m \in msgs: RecievePrepare(r, m))

EventuallyRecieveCommit == \A r \in Replica: WF_vars(\E m \in msgs: RecieveCommit(r, m))

\*EventuallyRecievePrepareOk == \A p \in Replica: WF_vars(\E m \in msgs: RecievePrepareOk(p, m))

LivenessSpec ==
    /\ EventuallyRecieveClientRequest
    /\ EventuallyRecievePrepare
    /\ EventuallyRecieveCommit
\*    /\ EventuallyRecievePrepareOk

-----------------------------------------------------------------------------

(* Full Spec *)

Spec == Init /\ [][Next]_vars \* /\ LivenessSpec

-----------------------------------------------------------------------------

VRNoMsgs == INSTANCE VR_without_message

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
\* Last modified Mon Mar 06 19:36:18 MSK 2023 by tycoon
\* Created Mon Nov 07 20:04:34 MSK 2022 by tycoon
