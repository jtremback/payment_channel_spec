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

EXTENDS Integers

VARIABLES
    \* @type: Set([type: Str, seq: Int, balance: Int, lastUpdate: [type: Str, seq: Int, balance: Int]]);
    msgs,               \* The set of all messages on the network
    \* @type: Str;
    contractPhase,
    \* @type: [type: Str, seq: Int, balance: Int];
    contractLastUpdate,
    \* @type: [type: Str, seq: Int, balance: Int];
    receiverLastUpdate,
    \* @type: [type: Str, seq: Int, balance: Int];
    senderLastUpdate

Messages == 
    [type: {"update"}, seq: Int, balance: Int] \union
    [type: {"close"}, lastUpdate: [type: {"update"}, seq: Int, balance: Int]] \union
    [type: {"challenge"}, lastUpdate: [type: {"update"}, seq: Int, balance: Int]]
    
\* Need to work on this
TypeOK == 
    /\  contractPhase \in {"open", "challenge", "closed"}
    /\  msgs \subseteq Messages
    /\  {contractLastUpdate, receiverLastUpdate, senderLastUpdate} \subseteq Messages

    
Init ==
    /\  msgs = {}
    /\  contractPhase = "open"
    /\  contractLastUpdate = [
            type |-> "update",
            seq |-> 0,
            balance |-> 0
        ]
    /\  receiverLastUpdate = [
            type |-> "update",
            seq |-> 0,
            balance |-> 0
        ]
    /\  senderLastUpdate = [
            type |-> "update",
            seq |-> 0,
            balance |-> 0
        ]

SenderPays ==
    /\  senderLastUpdate.seq < 11
    /\  LET m == [
            type |-> "update",
            seq |-> senderLastUpdate.seq + 1,
            balance |-> senderLastUpdate.balance + 10
        ]
        IN  /\  msgs' = msgs \union {m}
            /\  senderLastUpdate' = m
    /\  UNCHANGED <<contractPhase, contractLastUpdate, receiverLastUpdate>>

\*MessageLost == 
\*    /\  \E m \in msgs:
\*            msgs' = msgs \ {m}
\*    /\  UNCHANGED <<contractPhase, contractLastUpdate, senderLastUpdate, receiverLastUpdate>>

\*MessageLost ==
\*    \E m \in SUBSET msgs:
\*        msgs' = msgs \ m

ReceiverReceives ==
    /\ \E m \in msgs:
        /\  m.type = "update"
        /\  m.seq = receiverLastUpdate.seq + 1
        /\  m.balance >= receiverLastUpdate.balance
        /\  receiverLastUpdate' = m
    /\  UNCHANGED <<msgs, contractPhase, contractLastUpdate, senderLastUpdate>>

\* This is intended to capture both honest and dishonest closes.
\* The honest close is when the last message happens to be chosen,
\* the "dishonest" close is when any other message is chosen.
SomeoneCloses ==
    /\  \E m \in msgs:
            /\  m.type = "update"
            /\  msgs' = msgs \union {[ type |-> "close", lastUpdate |-> m ]}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, senderLastUpdate, receiverLastUpdate>>

ContractReceivesClose ==
    /\  contractPhase = "open"
    /\  \E m \in msgs:
        /\  m.type = "close"
        /\  contractPhase' = "challenge"
        /\  contractLastUpdate' = m.lastUpdate
    /\  UNCHANGED <<msgs, senderLastUpdate, receiverLastUpdate>>


\* We can just assume that the challenger is the receiver, since in a unidirectional channel,
\* only the sender has something to gain from an incorrect close, and wouldn't be challenging it
ReceiverChallenges ==
    /\  contractPhase = "challenge"
    /\  contractLastUpdate.seq < receiverLastUpdate.seq
    /\  msgs' = msgs \union {[ type |-> "challenge", lastUpdate |-> receiverLastUpdate ]}
    /\  UNCHANGED <<contractPhase, contractLastUpdate, senderLastUpdate, receiverLastUpdate>>
    
ContractReceivesChallenge ==
    /\  contractPhase = "challenge"
    /\  \E m \in msgs:
        /\  m.type = "challenge"
        /\  m.lastUpdate.seq > contractLastUpdate.seq
        /\  contractLastUpdate' = m.lastUpdate
    /\  UNCHANGED <<msgs, contractPhase, senderLastUpdate, receiverLastUpdate>>
        
FinalizeClose ==
    /\  contractPhase = "challenge"
    /\  contractPhase' = "closed"
    /\  UNCHANGED <<msgs, contractLastUpdate, senderLastUpdate, receiverLastUpdate>>

Next ==
    \/  SenderPays
\*    \/  MessageLost
    \/  ReceiverReceives
    \/  SomeoneCloses
    \/  ContractReceivesClose
    \/  ReceiverChallenges
    \/  ContractReceivesChallenge
    \/  FinalizeClose
  
=============================================================================
\* Modification History
\* Last modified Wed Jul 14 07:48:57 PDT 2021 by jehan
\* Created Fri Jul 09 10:49:41 PDT 2021 by jehan
