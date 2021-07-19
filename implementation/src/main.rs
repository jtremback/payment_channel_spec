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

#[derive(Serialize, Deserialize, Debug, Clone)]
struct UpdateMessage {
    update: Update,
    sender_sig: Option<Vec<u8>>,
    receiver_sig: Option<Vec<u8>>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
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
    receiver_url: Url,
    contract_url: Url,
    priv_key: Keypair,
    receiver_pub_key: PublicKey,
}

struct Receiver {
    last_update: UpdateMessage,
    contract_url: Url,
    priv_key: Keypair,
    sender_pub_key: PublicKey,
}

fn gen_keys() -> Keypair {
    let mut csprng = OsRng {};
    Keypair::generate(&mut csprng)
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

        self.phase = ContractPhase::Closed;
        self.last_update = Some(last_update);

        Ok(())
    }

    fn challenge(&self, last_update: UpdateMessage) -> Result<()> {
        Ok(())
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
