--------------------------- MODULE PaymentChannel ---------------------------
EXTENDS Integers

CONSTANT sender, receiver

\* VARIABLES 
\*     msgs,               \* The set of all messages on the network 
\*     contractState,      \* The state of the channel contract on the blockchain
\*     contractSeq,        \* What the contract thinks the sequence number is
\*     contractBalance,    \* What the contract thinks the balance is
\*     sndSeq,             \* What the sender thinks the sequence number is
\*     sndBalance,         \* What the sender thinks the balance of the channel is
\*     rcvSeq,             \* What the receiver thinks the sequence number is
\*     rcvBalance          \* What the receiver thinks the balance of the channel is

VARIABLES 
    msgs,               \* The set of all messages on the network 
    contractPhase,      
    contractLastMessage,
    sndLastMessage,
    rcvLastMessage,

\*    contractSeq,        \* What the contract thinks the sequence number is
\*    contractBalance,    \* What the contract thinks the balance is
\*    sndSeq,             \* What the sender thinks the sequence number is
\*    sndBalance,         \* What the sender thinks the balance of the channel is
\*    rcvSeq,             \* What the receiver thinks the sequence number is
\*    rcvBalance          \* What the receiver thinks the balance of the channel is

Messages == 
    [type: {"pay"}, seq: Int, balance: Int] \union
    [type: {"close"}, lastMessage: [type: {"pay"}, seq: Int, balance: Int]] \union
    [type: {"challenge"}, lastMessage: [type: {"pay"}, seq: Int, balance: Int]]
    
TypeOK == 
    /\  contractPhase \in {"open", "challenge", "closed"}
    /\  msgs \subseteq Messages
    
Init == 
    /\  msgs = {}
    /\  contractPhase = "open"
    /\  contractLastMessage = FALSE \* Not sure how to initialize a temporarily empty value, maybe this is ok
    /\  sndLastMessage = FALSE
    /\  rcvLastMessage = FALSE
    
SenderPays == 
    /\  sndSeq' = sndSeq + 1
    /\  sndBalance' = sndBalance + 17
    /\  msgs' = msgs \union {[
            type |-> {"pay"},
            seq |-> sndSeq + 1,
            balance |-> sndBalance + 17
        ]}
    /\  UNCHANGED <<contractState, rcvSeq, rcvBalance>>

MessageLost ==
    /\  msgs' = msgs \ { CHOOSE m \in msgs: TRUE }

ReceiverReceives ==
    /\  \E m \in msgs:
            /\  m.type = "pay"
            /\  m.seq = rcvSeq + 1
            /\  m.balance >= sndBalance
            /\  rcvSeq' = m.seq
            /\  rcvBalance' = m.balance
            /\  UNCHANGED <<contractState, sndSeq, sndBalance, msgs>>

SomeoneCloses ==
    /\  LET 

            
=============================================================================
\* Modification History
\* Last modified Mon Jul 12 10:36:48 PDT 2021 by jehan
\* Created Fri Jul 09 10:49:41 PDT 2021 by jehan
