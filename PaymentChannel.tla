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
    msgs,               \* The set of all messages on the network 
    contractState,      
    receiverState,
    senderState

Messages == 
    [type: {"update"}, seq: Int, balance: Int] \union
    [type: {"close"}, lastUpdate: [type: {"update"}, seq: Int, balance: Int]] \union
    [type: {"challenge"}, lastUpdate: [type: {"update"}, seq: Int, balance: Int]]
    
\* Need to work on this
\*TypeOK == 
\*    /\  contractPhase \in {"open", "challenge", "closed"}
\*    /\  msgs \subseteq Messages

    
Init ==
    /\  msgs = {}
    /\  contractState = [
            phase |-> "open",
            hasLastUpdate |-> FALSE
        ]
    /\  receiverState = [
            hasLastUpdate |-> FALSE
        ]
    /\  senderState = [
            hasLastUpdate |-> FALSE
        ]

SenderPays ==
    /\  LET m == [
            type |-> {"update"},
            seq |-> (IF receiverState.hasLastUpdate THEN receiverState.lastUpdate.seq ELSE 0) + 1,
            balance |-> (IF senderState.hasLastUpdate THEN senderState.lastUpdate.seq ELSE 0) + 17
        ]
        IN  /\  msgs' = msgs \union {m}
            /\  senderState' = [ senderState EXCEPT !["lastUpdate"] = m ]
    /\  UNCHANGED <<contractState, receiverState>>

MessageLost == 
    /\  \E m \in msgs:
            msgs' = msgs \ {m}
    /\  UNCHANGED <<contractState, senderState, receiverState>>

\*MessageLost ==
\*    \E m \in SUBSET msgs:
\*        msgs' = msgs \ m

ReceiverReceives ==
    /\ \E m \in msgs:
        /\  m.type = "update"
        /\  m.seq = (IF receiverState.hasLastUpdate THEN receiverState.lastUpdate.seq ELSE 0) + 1
        /\  m.balance >= (IF senderState.hasLastUpdate THEN senderState.lastUpdate.seq ELSE 0)
        /\  receiverState' = [ receiverState EXCEPT !["lastUpdate"] = m ]
    /\  UNCHANGED <<msgs, contractState, senderState>>

\* This is intended to capture both honest and dishonest closes.
\* The honest close is when the last message happens to be chosen,
\* the "dishonest" close is when any other message is chosen.
SomeoneCloses ==
    /\  \E m \in msgs:
            msgs' = msgs \union {[ type |-> "close", lastMessage |-> m ]}
    /\  UNCHANGED <<contractState, senderState, receiverState>>

ContractReceivesClose ==
    /\  contractState.phase = "open"
    /\  \E m \in msgs:
        /\  m.type = "close"
        /\  contractState' = [ contractState EXCEPT !["phase"] = "challenge", !["lastUpdate"] = m.lastUpdate ]
    /\  UNCHANGED <<msgs, senderState, receiverState>>


\* We can just assume that the challenger is the receiver, since in a unidirectional channel,
\* only the sender has something to gain from an incorrect close, and wouldn't be challenging it
ReceiverChallenges ==
    /\  contractState.phase = "challenge"
    /\  contractState.lastUpdate.seq < receiverState.seq
    /\  msgs' = msgs \union {[ type |-> "challenge", lastUpdate |-> receiverState.lastUpdate ]}
    /\  UNCHANGED <<contractState, senderState, receiverState>>
    
ContractReceivesChallenge ==
    /\  contractState.phase = "challenge"
    /\  \E m \in msgs:
        /\  m.type = "challenge"
        /\  m.lastUpdate.seq > contractState.lastUpdate.seq
        /\  contractState' = [ contractState EXCEPT !["lastUpdate"] = m.lastUpdate ]
    /\  UNCHANGED <<msgs, senderState, receiverState>>
        
FinalizeClose ==
    /\  contractState.phase = "challenge"
    /\  contractState' = [ contractState EXCEPT !["phase"] = "closed" ]
    /\  UNCHANGED <<msgs, senderState, receiverState>>

Next ==
    \/  SenderPays
    \/  MessageLost
    \/  ReceiverReceives
    \/  SomeoneCloses
    \/  ContractReceivesClose
    \/  ReceiverChallenges
    \/  ContractReceivesChallenge
    \/  FinalizeClose
  
=============================================================================
\* Modification History
\* Last modified Mon Jul 12 16:28:11 PDT 2021 by jehan
\* Created Fri Jul 09 10:49:41 PDT 2021 by jehan
