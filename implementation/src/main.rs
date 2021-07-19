use anyhow::{anyhow, Result};
use canonical_json::ser::to_string as to_canonical_str;
use ed25519_dalek::{Keypair, PublicKey, Signature, Signer, Verifier};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use serde_json;
use std::convert::TryFrom;
use url::Url;

fn main() {
    println!("Hello, world!");
    let contract = Contract {
        phase: ContractPhase::Open,
        last_update: None,
        receiver_pub_key: gen_keys().public,
        sender_pub_key: gen_keys().public,
    };
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

enum ContractPhase {
    Open,
    Challenge,
    Closed,
}

struct Contract {
    phase: ContractPhase,
    last_update: Option<UpdateMessage>,
    sender_pub_key: PublicKey,
    receiver_pub_key: PublicKey,
}

struct Sender {
    last_update: UpdateMessage,
    in_flight_update: UpdateMessage,
    first_update: UpdateMessage,
    priv_key: Keypair,
    receiver_pub_key: PublicKey,
}

struct Receiver {
    last_update: UpdateMessage,
    priv_key: Keypair,
    sender_pub_key: PublicKey,
    contract_phase: ContractPhase
}

fn gen_keys() -> Keypair {
    let mut csprng = OsRng {};
    Keypair::generate(&mut csprng)
}

fn make_sig<T: Serialize>(keypair: Keypair, message: T) -> Result<Vec<u8>> {
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
        if let Open = &self.phase {
        } else {
            return Err(anyhow!("Contract must be in open phase"));
        }

        check_sig(
            last_update
                .receiver_sig
                .ok_or_else(anyhow!("Update must have receiver signature"))?,
            self.receiver_pub_key,
            last_update.update.clone(),
        )?;
        check_sig(
            last_update
                .sender_sig
                .ok_or_else(anyhow!("Update must have sender signature"))?,
            self.sender_pub_key,
            last_update.update.clone(),
        )?;

        self.phase = ContractPhase::Challenge;
        self.last_update = Some(last_update);

        Ok(())
    }

    fn challenge(&self, last_update: UpdateMessage) -> Result<()> {
        if let Challenge = &self.phase {
        } else {
            return Err(anyhow!("Contract must be in challenge phase"));
        }

        check_sig(
            last_update
                .receiver_sig
                .ok_or_else(anyhow!("Update must have receiver signature"))?,
            self.receiver_pub_key,
            last_update.update.clone(),
        )?;
        check_sig(
            last_update
                .sender_sig
                .ok_or_else(anyhow!("Update must have sender signature"))?,
            self.sender_pub_key,
            last_update.update.clone(),
        )?;

        self.last_update = Some(last_update);

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
            update,
            sender_sig: Some(make_sig(self.priv_key, update)?),
            receiver_sig: None
        };

        self.in_flight_update = update_message;

        Ok(update_message)
    }

    fn receive_confirmation(&mut self, update_message: UpdateMessage) -> Result<()> {
        {
            // Erasing the sig in this scope for the purposes of comparison
            let update_message = UpdateMessage {
                receiver_sig: None,
                ..update_message
            };

            if self.in_flight_update != update_message {
                return Err(anyhow!("Update confirmation must match current in flight update"))
            };
        }

        check_sig(
            update_message
                .receiver_sig
                .ok_or_else(anyhow!("Update must have receiver signature"))?,
            self.receiver_pub_key,
            update_message.update.clone(),
        )?;

        self.last_update = update_message;

        Ok(())
    }

    fn close(&self, honest: bool) -> Result<CloseMessage> {
        if honest {
            Ok(CloseMessage {
                last_update: self.last_update
            })
        } else {
            Ok(CloseMessage {
                last_update: self.first_update
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
                .sender_sig
                .ok_or_else(anyhow!("Update must have sender signature"))?,
            self.sender_pub_key,
            update_message.update.clone(),
        )?;

        let update_message = UpdateMessage {
            receiver_sig: Some(make_sig(self.priv_key, update_message.update)?),
            ..update_message
        };

        self.last_update = update_message;

        Ok(update_message)
    }

    fn challenge(&self) -> Result<ChallengeMessage> {
        Ok(ChallengeMessage {
            last_update: self.last_update
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
            sender_sig: vec![1],
            receiver_sig: vec![1],
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
}
