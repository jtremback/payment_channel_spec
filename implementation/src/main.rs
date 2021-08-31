use anyhow::{anyhow, Result};
use canonical_json::ser::to_string as to_canonical_str;
use ed25519_dalek::{PublicKey, Signature, Signer, Verifier};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use serde_json;
use std::convert::TryFrom;
use url::Url;
use modelator::runner::TestRunner;
use std::ops::Deref;

fn main() {
    let tla_tests_file = "../PaymentChannel.tla";
    let tla_config_file = "../PaymentChannel.cfg";
    let options = modelator::Options::default();
    let traces = modelator::traces(tla_tests_file, tla_config_file, &options).unwrap();
    // println!("{}", traces[0]);

    let sender_priv_key = gen_keys();
    let receiver_priv_key = gen_keys();

    let first_update = Update {
        balance: 0,
        seq: 0
    };

    let first_update_message = UpdateMessage {
        update: first_update.clone(),
        receiver_sig: Some(make_sig(&receiver_priv_key, first_update.clone()).unwrap()),
        sender_sig: Some(make_sig(&sender_priv_key, first_update.clone()).unwrap())
    };

    println!("{:#?}", modelator::run(tla_tests_file, tla_config_file, &options, PaymentChannelTestRunner {
        contract: Contract {
            phase: ContractPhase::Open,
            last_update: first_update_message.clone(),
            receiver_pub_key: receiver_priv_key.public,
            sender_pub_key: sender_priv_key.public
        },
        sender: Sender {
            first_update: first_update_message.clone(),
            in_flight_update: first_update_message.clone(),
            last_update: first_update_message.clone(),
            receiver_pub_key: receiver_priv_key.public,
            priv_key: sender_priv_key.clone()
        },
        receiver: Receiver {
            contract_phase: ContractPhase::Open,
            last_update: first_update_message.clone(),
            sender_pub_key: sender_priv_key.public,
            priv_key: sender_priv_key
        },
        message: None
    }));
}

#[derive(Debug, Clone)]
struct PaymentChannelTestRunner {
    contract: Contract,
    sender: Sender,
    receiver: Receiver,
    message: Option<Message>
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum PaymentChannelAction {
    Init,
    SenderSendsPayment,
    MessageLost,
    ReceiverConfirmsPayment,
    SenderReceivesConfirmation,
    SenderHonestClose,
    ReceiverHonestClose,
    SenderDishonestClose,
    ContractReceivesClose,
    ReceiverChallenges,
    ContractReceivesChallenge,
    FinalizeClose
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum TLAContractPhase {
    open,
    challenge,
    closed
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TLAUpdateMessage {
    balance: u64,
    receiverSig: bool,
    senderSig: bool,
    seq: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TLACloseMessage {
    lastUpdate: TLAUpdateMessage
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TLAChallengeMessage {
    lastUpdate: TLAUpdateMessage
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
enum TLAMessage {
    #[serde(rename = "update")]
    Update(TLAUpdateMessage),
    #[serde(rename = "close")]
    Close(TLACloseMessage),
    #[serde(rename = "challenge")]
    Challenge(TLAChallengeMessage)
}

// {
//     "action": "FinalizeClose",
//     "contractLastUpdate": {
//       "balance": 1,
//       "receiverSig": true,
//       "senderSig": true,
//       "seq": 1,
//       "type": "update"
//     },
//     "contractPhase": "closed",
//     "msgs": [],
//     "receiverChallenged": true,
//     "receiverLastUpdate": {
//       "balance": 1,
//       "receiverSig": true,
//       "senderSig": true,
//       "seq": 1,
//       "type": "update"
//     },
//     "senderInFlightUpdate": {
//       "balance": 1,
//       "receiverSig": false,
//       "senderSig": true,
//       "seq": 1,
//       "type": "update"
//     },
//     "senderLastUpdate": {
//       "balance": 0,
//       "receiverSig": true,
//       "senderSig": true,
//       "seq": 0,
//       "type": "update"
//     }
//   }
#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentChannelStep {
    action: PaymentChannelAction,
    contractPhase: TLAContractPhase,
    msgs: Vec<TLAMessage>,
    receiverChallenged: bool,
    contractLastUpdate: TLAUpdateMessage,
    receiverLastUpdate: TLAUpdateMessage,
    senderLastUpdate: TLAUpdateMessage,
    senderInFlightUpdate: TLAUpdateMessage,
}

impl TestRunner<PaymentChannelStep> for PaymentChannelTestRunner {
    fn initial_step(&mut self, step: PaymentChannelStep) -> bool {
        println!("{:#?}", step);
        true
    }

    fn next_step(&mut self, step: PaymentChannelStep) -> bool {
        println!("{:#?}", step);

        match step.action {
            PaymentChannelAction::SenderSendsPayment => {
                self.message = Some(Message::Update(self.sender.send_payment(1).unwrap()))
            }
            PaymentChannelAction::ReceiverConfirmsPayment => {
                if let Message::Update(msg) = self.message.clone().unwrap() {
                    self.message = Some(Message::Update(self.receiver.confirm_payment(msg).unwrap()))
                } else {
                    panic!("wrong message type")
                }
            }
            PaymentChannelAction::SenderHonestClose => {
                self.message = Some(Message::Close(self.sender.close(true).unwrap()))
            }
            PaymentChannelAction::ContractReceivesClose => {
                if let Message::Close(msg) = self.message.clone().unwrap() {
                    self.contract.close(msg.last_update).unwrap()
                } else {
                    panic!("wrong message type")
                }
            }
            PaymentChannelAction::ReceiverChallenges => {
                self.message = Some(Message::Challenge(self.receiver.challenge().unwrap()))
            }
            PaymentChannelAction::ContractReceivesChallenge => {
                if let Message::Challenge(msg) = self.message.clone().unwrap() {
                    self.contract.challenge(msg.last_update).unwrap()
                } else {
                    panic!("wrong message type")
                }
            }
            // PaymentChannelAction::
            _ => unimplemented!()
        }

        true
    }
}

#[derive(Debug)]
struct Keypair(ed25519_dalek::Keypair);

impl Clone for Keypair {
    fn clone(&self) -> Self {
        Keypair(ed25519_dalek::Keypair::from_bytes(&self.0.to_bytes()).unwrap())
    }
}

impl Deref for Keypair {
    type Target = ed25519_dalek::Keypair;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(tag = "type")]
enum Message {
    Update(UpdateMessage),
    Close(CloseMessage),
    Challenge(ChallengeMessage),
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct UpdateMessage {
    update: Update,
    sender_sig: Option<Vec<u8>>,
    receiver_sig: Option<Vec<u8>>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Update {
    seq: u64,
    balance: u64,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct CloseMessage {
    last_update: UpdateMessage,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct ChallengeMessage {
    last_update: UpdateMessage,
}

#[derive(Debug, Clone, Deserialize)]
enum ContractPhase {
    Open,
    Challenge,
    Closed,
}

#[derive(Debug, Clone)]
struct Contract {
    phase: ContractPhase,
    last_update: UpdateMessage,
    sender_pub_key: PublicKey,
    receiver_pub_key: PublicKey,
}

#[derive(Debug, Clone)]
struct Sender {
    last_update: UpdateMessage,
    in_flight_update: UpdateMessage,
    first_update: UpdateMessage,
    priv_key: Keypair,
    receiver_pub_key: PublicKey,
}

#[derive(Debug, Clone)]
struct Receiver {
    last_update: UpdateMessage,
    priv_key: Keypair,
    sender_pub_key: PublicKey,
    contract_phase: ContractPhase
}

fn gen_keys() -> Keypair {
    let mut csprng = OsRng {};
    Keypair(ed25519_dalek::Keypair::generate(&mut csprng))
}

fn make_sig<T: Serialize>(keypair: &Keypair, message: T) -> Result<Vec<u8>> {
    Ok(keypair.sign(
        to_canonical_str(&serde_json::to_value(message)?)?.as_bytes()
    ).to_bytes().to_vec())
}

fn check_sig<T: Serialize>(sig: Vec<u8>, pubkey: PublicKey, message: T) -> Result<()> {
    let sig: &[u8] = &sig;
    let sig: Signature = Signature::try_from(sig)?;
    pubkey.verify(
        to_canonical_str(&serde_json::to_value(message)?)?.as_bytes(),
        &sig,
    )?;
    Ok(())
}

impl Contract {
    fn close(&mut self, last_update: UpdateMessage) -> Result<()> {
        match &self.phase {
            ContractPhase::Open => {}
            _ => { return Err(anyhow!("Contract must be in open phase")); }
        }

        check_sig(
            last_update
                .receiver_sig.clone()
                .ok_or_else(|| anyhow!("Update must have receiver signature"))?,
            self.receiver_pub_key,
            last_update.update.clone(),
        )?;
        check_sig(
            last_update
                .sender_sig.clone()
                .ok_or_else(|| anyhow!("Update must have sender signature"))?,
            self.sender_pub_key,
            last_update.update.clone(),
        )?;

        self.phase = ContractPhase::Challenge;
        self.last_update = last_update;

        Ok(())
    }

    fn challenge(&mut self, last_update: UpdateMessage) -> Result<()> {
        match &self.phase {
            ContractPhase::Challenge => {}
            _ => { return Err(anyhow!("Contract must be in challenge phase")); }
        }
        check_sig(
            last_update
                .sender_sig.clone()
                .ok_or_else(|| anyhow!("Update must have sender signature"))?,
            self.sender_pub_key,
            last_update.update.clone(),
        )?;
        println!("hello");
        check_sig(
            last_update
            .receiver_sig.clone()
            .ok_or_else(|| anyhow!("Update must have receiver signature"))?,
            self.receiver_pub_key,
            last_update.update.clone(),
        )?;

        self.last_update = last_update;

        Ok(())
    }
    
    fn finalize_close(&mut self) -> Result<()> {
        if let ContractPhase::Challenge = self.phase {} else {
            return Err(anyhow!("Must be in challenge phase to finalize close"))
        }

        self.phase = ContractPhase::Closed;

        Ok(())
    }
}

impl Sender {
    fn send_payment(&mut self, amount: u64) -> Result<UpdateMessage> {
        let update = Update {
            balance: self.last_update.update.balance + amount,
            seq: self.last_update.update.seq + 1
        };

        let update_message = UpdateMessage {
            update: update.clone(),
            sender_sig: Some(make_sig(&self.priv_key, update.clone())?),
            receiver_sig: None
        };

        self.in_flight_update = update_message.clone();

        Ok(update_message)
    }

    fn receive_confirmation(&mut self, update_message: UpdateMessage) -> Result<()> {
        {
            // Erasing the sig in this scope for the purposes of comparison
            let update_message = UpdateMessage {
                receiver_sig: None,
                ..update_message.clone()
            };

            if self.in_flight_update != update_message {
                return Err(anyhow!("Update confirmation must match current in flight update"))
            };
        }

        check_sig(
            update_message
                .receiver_sig.clone()
                .ok_or_else(|| anyhow!("Update must have receiver signature"))?,
            self.receiver_pub_key,
            update_message.update.clone(),
        )?;

        self.last_update = update_message;

        Ok(())
    }

    fn close(&self, honest: bool) -> Result<CloseMessage> {
        if honest {
            Ok(CloseMessage {
                last_update: self.last_update.clone()
            })
        } else {
            Ok(CloseMessage {
                last_update: self.first_update.clone()
            })
        }
    }
}

impl Receiver {
    fn confirm_payment(&mut self, update_message: UpdateMessage) -> Result<UpdateMessage> {
        if !(update_message.update.balance >= self.last_update.update.balance) {
            return Err(anyhow!("Update must have greater or equal channel balance"))
        }

        if !(update_message.update.seq > self.last_update.update.seq) {
            return Err(anyhow!("Update must have greater sequence number"))
        }

        check_sig(
            update_message
                .sender_sig.clone()
                .ok_or_else(|| anyhow!("Update must have sender signature"))?,
            self.sender_pub_key,
            update_message.update.clone(),
        )?;

        let new_update_message = UpdateMessage {
            receiver_sig: Some(make_sig(&self.priv_key, update_message.update.clone())?),
            ..update_message
        };

        self.last_update = new_update_message.clone();

        Ok(new_update_message)
    }

    fn challenge(&self) -> Result<ChallengeMessage> {
        Ok(ChallengeMessage {
            last_update: self.last_update.clone()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json;
    #[test]
    fn protocol_serialization() {
        let update = UpdateMessage {
            update: Update { seq: 0, balance: 0 },
            sender_sig: Some(vec![1]),
            receiver_sig: Some(vec![1]),
        };
        let test_values: Vec<Message> = vec![
            Message::Update(update.clone()),
            Message::Close(CloseMessage {
                last_update: update.clone(),
            }),
            Message::Challenge(ChallengeMessage {
                last_update: update.clone(),
            }),
        ];

        for value in test_values {
            let serialized = serde_json::to_string(&value).unwrap();
            println!("serialized = {}", serialized);

            // Convert the JSON string back to a Protocol message
            let deserialized: Message = serde_json::from_str(&serialized).unwrap();

            // assert_eq!(value, deserialized);
        }
    }
    #[test]
    fn step_serialization() {
        let data = r#"{
            "action": "SenderSendsPayment",
            "contractLastUpdate": {
              "balance": 0,
              "receiverSig": true,
              "senderSig": true,
              "seq": 0,
              "type": "update"
            },
            "contractPhase": "challenge",
            "msgs": [
              {
                "balance": 1,
                "receiverSig": false,
                "senderSig": true,
                "seq": 1,
                "type": "update"
              }
            ],
            "receiverChallenged": false,
            "receiverLastUpdate": {
              "balance": 1,
              "receiverSig": true,
              "senderSig": true,
              "seq": 1,
              "type": "update"
            },
            "senderInFlightUpdate": {
              "balance": 1,
              "receiverSig": false,
              "senderSig": true,
              "seq": 1,
              "type": "update"
            },
            "senderLastUpdate": {
              "balance": 0,
              "receiverSig": true,
              "senderSig": true,
              "seq": 0,
              "type": "update"
            }
          }"#;

        let deserialized: PaymentChannelStep = serde_json::from_str(&data).unwrap();

        println!("{:#?}", deserialized);
    }
}
