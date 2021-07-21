--------------------------- MODULE PaymentChannel ---------------------------
\*This is a specification of a unidirectional payment channel. A payment channel is a
\*scheme to exchange a large number of payments between two parties while publishing
\*only one transaction to the blockchain. A unidirectional payment channel means that
\*one of the parties has the role of receiver while the other has the role of sender.
\*
\*First, the sender locks up some money in a smart contract on the blockchain. This
\*contract will release some or all of this money to the receiver, if it receives
\*an "update" message signed by the sender specifying how much money to release. Before the
\*money is released, there is a challenge period of some amount of time. During this
\*time the contract will accept any later update (with a higher value of "seq").
\*
\*This is to foil an attack where the sender closes the channel with an old update, so that
\*the receiver does not receive as much money as it should. In this case, the receiver could
\*submit the later update to the contract during the challenge period, resulting in 
\*the full amount being released.

\* https://github.com/cosmos/ibc-go/blob/main/modules/apps/transfer/keeper/relay_model/relay_tests.tla

EXTENDS Integers, TLC

VARIABLES
    \* @type: Set([type: Str, seq: Int, balance: Int, lastUpdate: [type: Str, seq: Int, balance: Int]]);
    msgs,
    \* @type: Str;
    contractPhase,
    \* @type: [type: Str, seq: Int, balance: Int];
    contractLastUpdate,
    \* @type: [type: Str, seq: Int, balance: Int];
    receiverLastUpdate,
    \* @type: [type: Str, seq: Int, balance: Int];
    senderLastUpdate,
    \* @type: [type: Str, seq: Int, balance: Int];
    senderInFlightUpdate,
    \* @type: BOOLEAN
    receiverChallenged

\* UNCHANGED <<msgs, contractPhase, contractLastUpdate, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>

UpdateMessage == [type: {"update"}, seq: 0..5, balance: 0..5, senderSig: BOOLEAN, receiverSig: BOOLEAN]

Messages == 
    UpdateMessage \union
    [type: {"close"}, lastUpdate: UpdateMessage] \union
    [type: {"challenge"}, lastUpdate: UpdateMessage]

\* Invariants
TypeOK == 
    /\  contractPhase \in {"open", "challenge", "closed"}
    /\  msgs \subseteq Messages
    /\  {contractLastUpdate, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate} \subseteq Messages

\* Channel should not close with an update that doesn't match the sender and the receiver's latest update
UpdatesMatch == 
    (contractPhase = "closed" /\  receiverChallenged) =>
        /\  contractLastUpdate = receiverLastUpdate

HappyPathTest ==
    /\  contractPhase = "closed"
    /\  receiverChallenged
    /\  contractLastUpdate = receiverLastUpdate

HappyPathNeg == ~HappyPathTest

Init ==
    /\  msgs = {}
    /\  contractPhase = "open"
    /\  contractLastUpdate = [
            type |-> "update",
            seq |-> 0,
            balance |-> 0,
            senderSig |-> TRUE,
            receiverSig |-> TRUE
        ]
    /\  receiverLastUpdate = [
            type |-> "update",
            seq |-> 0,
            balance |-> 0,
            senderSig |-> TRUE,
            receiverSig |-> TRUE
        ]
    /\  senderLastUpdate = [
            type |-> "update",
            seq |-> 0,
            balance |-> 0,
            senderSig |-> TRUE,
            receiverSig |-> TRUE
        ]
    /\  senderInFlightUpdate = [
            type |-> "update",
            seq |-> 0,
            balance |-> 0,
            senderSig |-> TRUE,
            receiverSig |-> TRUE
        ]
    /\  receiverChallenged = FALSE

SenderSendsPayment ==
    /\  senderLastUpdate.seq < 5
    /\  LET m == [
            type |-> "update",
            seq |-> senderLastUpdate.seq + 1,
            balance |-> senderLastUpdate.balance + 1,
            senderSig |-> TRUE,
            receiverSig |-> FALSE
        ]
        IN  /\  msgs' = {m}
            /\  senderInFlightUpdate' = m
    /\  UNCHANGED <<contractPhase, contractLastUpdate, receiverLastUpdate, senderLastUpdate, receiverChallenged>>

MessageLost == 
    /\  msgs' = {}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>

ReceiverConfirmsPayment ==
    /\  contractPhase = "open"
    /\ \E m \in msgs:
        /\  m.type = "update"
        /\  m.seq = receiverLastUpdate.seq + 1
        /\  m.balance >= receiverLastUpdate.balance
        /\  m.senderSig = TRUE
        /\  m.receiverSig = FALSE
        /\  receiverLastUpdate' = [m EXCEPT !["receiverSig"] = TRUE]
        /\  msgs' = {[m EXCEPT !["receiverSig"] = TRUE]}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>

SenderReceivesConfirmation ==
    /\ \E m \in msgs:
        /\  m = [senderInFlightUpdate EXCEPT !["receiverSig"] = TRUE]
        /\  senderLastUpdate' = m
        /\  msgs' = {}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, receiverLastUpdate, senderInFlightUpdate, receiverChallenged>>

SenderHonestClose ==
    /\  msgs' = {[ type |-> "close", lastUpdate |-> senderLastUpdate ]}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>

ReceiverHonestClose ==
    /\  msgs' = {[ type |-> "close", lastUpdate |-> receiverLastUpdate ]}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>

SenderDishonestClose ==
    /\  msgs' = {[ type |-> "close", lastUpdate |-> [
            type |-> "update",
            seq |-> 0,
            balance |-> 0,
            senderSig |-> TRUE,
            receiverSig |-> TRUE
        ]]}

ContractReceivesClose ==
    /\  contractPhase = "open"
    /\  \E m \in msgs:
        /\  m.type = "close"
        /\  m.lastUpdate.senderSig = TRUE
        /\  m.lastUpdate.receiverSig = TRUE
        /\  contractPhase' = "challenge"
        /\  contractLastUpdate' = m.lastUpdate
        /\  msgs' = {}
    /\  UNCHANGED <<receiverLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>


\* We can just assume that the challenger is the receiver, since in a unidirectional channel,
\* only the sender has something to gain from an incorrect close, and wouldn't be challenging it
ReceiverChallenges ==
    /\  contractPhase = "challenge"
    /\  contractLastUpdate.seq < receiverLastUpdate.seq
    /\  msgs' = {[ type |-> "challenge", lastUpdate |-> receiverLastUpdate ]}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>
    
ContractReceivesChallenge ==
    /\  contractPhase = "challenge"
    /\  \E m \in msgs:
        /\  m.type = "challenge"
        /\  m.lastUpdate.senderSig = TRUE
        /\  m.lastUpdate.receiverSig = TRUE
        /\  m.lastUpdate.seq > contractLastUpdate.seq
        /\  contractLastUpdate' = m.lastUpdate
        /\  msgs' = {}
        /\  receiverChallenged' = TRUE
    /\  UNCHANGED <<contractPhase, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate>>
        
FinalizeClose ==
    /\  contractPhase = "challenge"
    /\  contractPhase' = "closed"
    /\  UNCHANGED <<msgs, contractLastUpdate, receiverLastUpdate, senderLastUpdate, senderInFlightUpdate, receiverChallenged>>

Next ==
    \/  SenderSendsPayment
    \/  MessageLost
    \/  ReceiverConfirmsPayment
    \/  SenderReceivesConfirmation
    \/  SenderHonestClose
    \/  ReceiverHonestClose
    \/  ContractReceivesClose
    \/  ReceiverChallenges
    \/  ContractReceivesChallenge
    \/  FinalizeClose
  
=============================================================================
\* Modification History
\* Last modified Wed Jul 14 07:48:57 PDT 2021 by jehan
\* Created Fri Jul 09 10:49:41 PDT 2021 by jehan
