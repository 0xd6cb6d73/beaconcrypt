# Overview
This document describes the way beaconcrypt exposes state persistence to the server. This breaks forward secrecy, but is required to be useful in a server context. Additionally, the [threat model](threat_model.md) specifies that we already assume that server compromise is game over.

# Usage
The server object exposes an `export_state` method, which produces the following JSON output:
```json
{
    "identity_key": [1,14,[65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65]],
    "identity_key_kid": 0,
    "server_kid": 2,
    "known_ids": {
      "1": {
        "pk": [1,179,176,97,56,138,132,165,3,79,7,190,144,179,105,2,187,3,165,119,87,142,123,131,59,254,117,167,156,41,125,254,56],
        "ratchet": {
            "send_key": [6,8,[1,79,112,132,98,47,6,118,212,221,235,120,149,156,87,172,106,157,248,36,135,198,191,207,243,65,83,183,57,110,161,213]],
            "recv_key": [6,9,[171,11,55,200,145,194,88,3,54,90,129,116,208,31,217,146,194,6,40,38,184,222,233,43,198,132,151,204,51,182,233,11]],
            "send_ctr": 2,
            "recv_past": {},
            "recv_ctr": 1
        }
    },
      "2": {
        "pk": [1,198,247,65,172,172,76,66,155,64,140,90,73,162,40,247,225,134,162,239,15,149,105,64,89,167,171,159,125,28,56,207,166],
        "ratchet": {
            "send_key": [6,8,[62,234,153,109,200,24,60,67,197,43,127,175,32,40,158,53,61,233,196,100,226,72,64,51,164,91,186,161,85,15,211,144]],
            "recv_key": [6,9,[102,95,139,78,169,159,72,133,153,83,238,26,138,13,31,122,136,212,63,38,104,40,239,153,128,61,177,149,28,80,14,79]],
            "send_ctr": 2,
            "recv_past": {},
            "recv_ctr": 1
        }
      }
    },
    "consumed_registrations": [
      [179,176,97,56,138,132,165,3,79,7,190,144,179,105,2,187,3,165,119,87,142,123,131,59,254,117,167,156,41,125,254,56,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],
      [198,247,65,172,172,76,66,155,64,140,90,73,162,40,247,225,134,162,239,15,149,105,64,89,167,171,159,125,28,56,207,166,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20]
    ]
}
```

`identity_key` contains the server's 32-byte Ed25519 seed as a strongly typed array. `identity_key_kid` is the server identity's key ID, `server_kid` is the last allocated remote-ID counter, and `known_ids` contains the known beacons' ratchet state. In this example the server knows about 2 beacons, with keyId 1 and 2. Every `known_ids` entry contains the beacon's public key as well as the full state of its associated ratchets.

Each serialized `RatchetManager` has exactly five fields: `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`. Send-message keys and their logical capabilities exist only during one encryption call and are never persisted. This is an intentional schema break: objects from the former six-field format, including objects with an empty `send_past`, are rejected and must not be used to restore this version.

`consumed_registrations` is the persistent replay history. Each sorted 64-byte
entry is the decoded beacon identity followed by the decoded signed one-time
X25519 public key from one accepted `InitKex`. An identifier is retained even
when response construction fails or its peer is later deleted. Restoration
rejects a missing history, entries of the wrong length, duplicates, or fewer
entries than committed peers. This field was added in Stage 5; pre-Stage-5
snapshots are intentionally rejected rather than silently restoring without
replay protection. Together these fields allow `from_state` to restore the
server from the serialized state alone.

Note that the ratchet keys are strongly-typed arrays, which server code should not try to parse. I expect that this method would be rather slow, as it will extract and serialize the entirety of the beaconcrypt instance's crypto state. Therefore, the server has access to the following interface:

```rust
/// Encrypt some bytes to `kid` and return the ciphertext, `kid`, consumed key sequence,
/// and complete ratchet state for `kid`.
fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<SendState>;
/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
/// and return the plaintext, `kid`, consumed key sequence, and complete ratchet state for `kid`.
fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<RecvState>;
```

The returned type looks like this:
```rust
pub struct StateUpdate<Role: roles::ChainKey> {
	pub kid: u64,
	/// The sequence number of the key consumed by this operation.
	pub seq: u64,
	pub state: RatchetManager,
	pub data: Vec<u8>,
	pub(crate) _role: PhantomData<Role>,
}

pub type SendState = StateUpdate<roles::ChainSendKey>;
pub type RecvState = StateUpdate<roles::ChainRecvKey>;
```

This type is wrapped by the various bindings to provide native structs. However, there is also a JSON interface:
```rust
/// Encrypt some bytes to `kid` and return the ciphertext, `kid`, consumed key sequence,
/// and complete ratchet state for `kid` as a JSON string.
fn encrypt_and_update_json(&mut self, bytes: &[u8], kid: u64) -> Option<String>;
/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
/// and return the plaintext, `kid`, consumed key sequence, and complete ratchet state for `kid`
/// as a JSON string.
fn decrypt_and_update_json(&mut self, bytes: &[u8]) -> Option<String>;
```

The Python and Go wrappers expose the complete `RatchetManager` as JSON through `EncryptState.state()` and `EncryptState.State`, respectively.

The JSON output looks like this:
```json
{
    "kid": 1,
    "seq": 2,
    "state": {
        "send_key": [6,8,[194,31,149,100,15,174,115,69,241,227,96,72,201,19,141,95,213,196,143,140,70,161,199,45,22,161,169,84,122,48,176,236]],
        "recv_key": [6,9,[171,11,55,200,145,194,88,3,54,90,129,116,208,31,217,146,194,6,40,38,184,222,233,43,198,132,151,204,51,182,233,11]],
        "send_ctr": 2,
        "recv_past": {},
        "recv_ctr": 1
    },
    "data": [0,0,0,0,19,0,0,0,0,0,0,0,2,0,1,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,154,3,0,0,56,233,14,12,69,80,85,248,14,234,235,...]
}
```
This provides a more efficient interface for server implementations to update one beacon's persisted state than extracting every known beacon. The snapshot includes both ratchet chain states and any cached skipped receive-message keys, and its keys use the same strongly typed format as the full export.
