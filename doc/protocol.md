<!-- SPDX-License-Identifier: 0BSD -->

# Overview
The protocol uses signal's `PQXDH` for key establishment alongside a symmetric ratchet to generate message keys. Every encryption uses a new key derived from the ratchet using an AEAD scheme. It is implemented on top of `libsodium`. The interface provides opaque byte strings that either party can put on the wire. The intent is to provide a generic cryptographic layer, upon which you can use whatever your beacon speaks. Unfortunately, Mythic requires some bookeeping information (a UUID) to be prepended to any message, so that will have to be added regardless and will not be protected. I don't know enough about sliver, CS, havoc or any other framework to say anything about them.

## Assumptions
It is assumed that the server's identity public key is compiled with beacon.

## Motivation for dropping certain properties
The signal protocol, which is to say `PQXDH` + `triple ratchet`, is proven to provide two important properties: Forward Security (`FS`), and Post-Compromise Security (`PCS`). The former means that an attacker cannot learn how to decrypt previous messages by compromising a participant in beaconcrypt at a given point in time. The latter means that an attacker cannot learn how to decrypt future messages by compromising a participant in beaconcrypt at a given point in time. In the context of a C2 protocol, `PCS` seems unnecessary. Indeed, if an attacker can access the current cryptographic state of the application, one of two things has happened. First, they have compromised our beacon. At this point, the attacker can either run whatever they want themselves, or through our beacon and we have failed at preventing the attacker from injecting arbitrary commands. However, the attacker cannot read past messages because of `FS`, so the confidentiality of data that was previously exfiltrated is preserved provided they cannot just access it themselves. In the second case, the attacker has compromised the C2 server. This is game over with any C2 server I'm aware of, as at this point the attacker has access to all the data that was exfiltrated and can task any beacon the server knows about. It is this analysis that leads to `PCS` being dropped from the requirements for this protocol, while `FS` remains desirable. Another point is that `triple ratchet`, the PQ Continuous Key Agreement (`CKA`) mechanism used by signal is quite complicated and requires a lot of state management, which just smells like logic bugs to me.

Additionally, the signal protocol also provides something called `message commitment`. Authenticated encryption with associated data (AEAD) has the property that two plaintexts encrypted under two different keys can generate the same ciphertext and authentication tag. This may allow an attacker to exploit a confused deputy to get one principal to obtain a different message than other participants. This attack is often called `invisible salamanders`. Beaconcrypt provides strong commitment, that is to say it commits to the key, nonce, associated data and message through the use of [Chan and Rogaway's `CTX` scheme](https://eprint.iacr.org/2022/1260). The `CTX` scheme is slightly modified, in that beaconcrypt still transmits the original AEAD tag alonside the `CTX` tag. This is done to remain compatible with the public libsodium interface.

## Primitives
| Purpose | Primitive | Bit strength | Rationale |
|--|--|--|--|
| Signature | Ed25519 | 128 | Widely adopted internet standard, small size and high performance |
| Classical KEM | X25519 | 128 | Widely adopted internet standard, small size and high performance |
| PQ KEM| ML-KEM-768 | 192| NIST standard, standardized in TLS as part of xwing (ML-KEM + X25519) |
| Key derivation | HKDF-SHA512 | N/A | PQXDH specifies the use of HKDF |
| Authenticated encryption | ChaCha20-Poly1305 (IETF) | 256 | Used in the TLS 1.3 standard |

# Session establishment
This is the entry point to beaconcrypt and it is initiated by the beacon. The beacon generates a Ed25519 keypair, called the identity key, which will serve as its cryptographic identity for the entire duration of beaconcrypt. The beacon then crafts a `phase1` bundle containing all the public keys necessary for a `PQXDH` protocol run. This bundle contains a ML-KEM public key, and so is rather large. This is analogous to the step where Bob uploads their public parameters to the server in the signal protocol documentation, with the following modifications:
- There are no random `Z` values as XEdDSA is not used, so we convert Ed25519 keys to X25519 format for the DH steps
- There are no explicit key identifiers, as beaconcrypt treats public keys are identifiers 
- There is only a single one-time key, as the beacon can only ever communicate with one remote party
- There are no explicit signatures, as we use the libsodium idiomatic form of `signature || buffer`

The server uses these values to perform its leg of the `PQXDH` protocol and initializes its KDF chains using the shared secret. It uses its send chain to derive an encryption key for the initial message, then ratchets. It then sends the relevant public values and the newly-obtained cipher text in the `phase2` bundle.

The beacon receives the initial message and uses the `phase2` bundle to perform the final leg of the `PQXDH` protocol run. It uses the shared secret to initialize its KDF chains, then attempts to decrypt the bundled ciphertext using its receive chain. If this is successful, the session is established. At this point, the beacon and the server share symmetric cryptographic material that they can use to ratchet forward and rotate keys per message, without involving assymetric crypto.

# Message encryption
Every time something is encrypted, it is wrapped in a Cap’n Proto message called a `CryptoFrame`. This embeds minor metadata that allows managing out-of order messages. Every `CryptoFrame` is encrypted under a distinct key, obtained from the principal's `send` KDF chain, which is then ratcheted forward. Nonces are also obtained from the KDF chain, because keys are only used once there is no possible reuse. Keys are deleted once they have been used, this is always immediate for keys on the `send` chains. Keys on the `receive` chains might need to be kept for longer in cases where multiple messages are recieved out of order, in which case the implementation needs to ratchet forward to the required sequence nmuber. All the intermediate keys need to be saved by the implementation, such that they can be used to decrypt the other messages when they are processed. This skipping must be constrained to some gap between the current known counter and the target, to avoid potential unbounded memory consumption. The encryption uses an AEAD scheme, as such, the content of the plaintext is authenticated. However, this scheme doesn't provide the following:
- Authenticated `CryptoFrame` metadata

While the `CryptoFrame` contains little information, an active attacker might trivially perform a DoS attack by modifiying the sequence number to trigger excessive ratcheting. As such, it is recommended to use the signature layer to ensure this metadata is protected.

# Protocol message
## ProtoGram
This is intended to be the top level message when the caller opts to use digital signatures. It is defined in [protogram.capnp](../src/schema/protogram.capnp). Its role is to tell the reader which cryptographic identity signed the `data` member. Cryptographic identities are identified using a single 64 unsigned integer, often called `keyId` or `kid`. When signature is opted into, the reader must look up the cryptographic identity associated with the `keyId` and verify that the signature over `data` is valid for that identity (e.g. that the public key can verify the signature). Once this is done, the reader can use the contents of the `data` member for any purpose, although the intent is for it to carry a serialized `CryptoFrame`.

## CryptoFrame
This is the most basic framing for an encrypted message within beaconcrypt. It is defined in [cryptoframe.capnp](../src/schema/cryptoframe.capnp). It carries a key identifier (`seq`), a direction flag `sToB` or `stob` and the encrypted data under `cipherText`. These messages are closely tied to the ratcheting mechanism. To create such a message, the writer must:
- Ratchet their `send` keychain forward
- Use their current `send` key to encrypt the message into a pair of temporary variables `CT` and `T` 
- Compute the commitment `T*` using `Hash(Key, Nonce, Associated Data, T)`
  - The hash function is Blake2b with a 512bit output length
- Append `T` and `T*` to `CT` and place the resulting buffer in `cipherText`
- Set `seq` to the number of the current key
- Set `sToB` to true if the writer is a server or to false if the writer is a beacon
- Delete the current `send` key

To read a `CryptoFrame`, the reader must:
- Check that the direction flag `sToB` is true if the reader is a beacon or false if the reader is a server
  -  Abort processing if there is a mismatch
- Check that the difference between `seq` and the current sequence number of the `recv` chain is acceptable
  -  The reference implementation tolerates ratcheting up to 50 keys forward, this number was pulled out of a hat
  - Abort processing if the difference is too large
- Ratchet their `recv` keychain forward to `seq`
- Extract `CT`, `T` and `T*` from the `cipherText` field
- Compute the commitment `T*'` using `Hash(Key, Nonce, Associated Data, T)`
  - The hash function is Blake2b with a 512bit output length
- Perform a constant-time comparison of `T*` and `T*'`
  - Abort processing if there is a mismatch
- Use the key associated with `seq` to decrypt 
- Delete the `seq` key on their `recv` keychain if decryption was successful

## InitKex
This message starts the beacon registration process by initiating the `PQXDH` protocol run. It is defined in [phase1.capnp](../src/schema/phase1.capnp).It must only be run once per beacon instance. It is appropriate to send this message by itself to the server, once serialized, even if user otherwise opts into digital signatures for the rest of the protocol. The beacon must generate all relevant cryptographic keys using the appropriate libsodium API before trying to construct this message. When referring to encoded public keys, it is meant that the caller will prepend a byte indicating the type of the key before the public key buffer. The same is true when speaking of encoded KEM keys. The beacon builds this message as follows:
- Set `identityKey` to the beacon's Ed25519 encoded identity public key
- Set `preKey` to the beacon's X25519 encoded prekey public key signed under the beacon's identity key
- Set `oneTimeKey` to the beacon's X25519 encoded onetime public key signed under the beacon's identity key
- Set `pqKey` to the beacon's ML-KEM-768 encoded ML-KEM public key signed under the beacon's identity key

Beaconcrypt assumes the use of the libsodium `sign` API for all signatures. In this scheme, the signature is prepended to the buffer, so there are no dedicated signature fields.

The server must use this message as follows:
- Verify that all keys except `identityKey` are signed under `identityKey`
- Generate its ephemeral X25519 keypair
- Encapsulate the PQ shared secret (`SS`) using `pqKey`
- Convert the beacon's identity public key and the server's identity secret key to X25519 format using libsodium's `ed25519_pk_to_curve25519` and `ed25519_sk_to_curve25519` respectively (thereafter they will use the `_kex` suffix)
- Perform the 4 Diffie Hellman rounds
  - dh1 = DH(`server_id_sk_kex`, `beacon_prekey_pk`)
  - dh2 = DH(`ephemeral_sk`, `beacon_id_pk_kex`)
  - dh3 = DH(`ephemeral_sk`, `beacon_prekey_pk`)
  - dh4 = DH(`ephemeral_sk`, `beacon_onetime_pk`)
- Compute the derived secret `KDF(Padding || DH1 || DH2 || DH3 || DH4 || SS)` using the PQXDH protocol string as HKDF `info`
  - `Padding` is 32 `0xFF` bytes
- Return the KEM ciphertext, derived secret, ephemeral public key and beacon public key

## KexResponse
This message enables the beacon to obtain the elements it needs to derive the shared secret. It is defined in [phase2.capnp](../src/schema/phase2.capnp) It is intrinsically linked to the corresponding `InitKex` which intiated the protocol run. It is expected that the server will create this message immediately after parsing a valid `InitKex`. It also potentially carries the first of the server's messages to the beacon. The server must contruct it as follows:
- Create a new key ID to assign to the beacon
- Register a new known cryptographic identity using the beacon's public key and newly created key ID
  - At this point, the beacon is registered from the point of view of beaconcrypt
- Initialize its side of the ratchets using the derived secret with the symmetric ratchet protocol string as HKDF `info`
- Set the `keyId` field to the newly generate beacon's key ID
- Set the `ephemeralKey` field to the X25519 ephemeral public key from the corresponding `InitKex`
- Set the `identityKey` to the server's Ed25519 public key
- Set the `kemCipherText` to the KEM ciphertext from the corresponding `InitKex`
- Create the associated data byte string by concatenating the encoded server identity key, encoded beacon identity key and the PQXDH and symmetric ratchet protocol strings
- Encrypt the first message if there is one, otherwise encrypt a single `0xFF` byte using a `CryptoFrame` and set `appCipherText` to its value
- Return the beacon's public key and key ID to the caller so it can register it as required

Upon reception, the beacon must process this message as follows:
- Decapsulate the shared PQ secret using `kemCipherText` adn the beacon's KEM secret key
- Convert the beacon's identity secret key and the server's identity public key from `identityKey` to X25519 format using libsodium's `ed25519_sk_to_curve25519` and `ed25519_pk_to_curve25519` respectively (thereafter they will use the `_kex` suffix)
- Compute the 4 Diffie Hellman rounds
  - dh1 = DH(`beacon_prekey_sk`, `server_id_pk_kex`)
  - dh2 = DH(`beacon_id_sk_kex`, `server_ephemeral_pk`)
  - dh3 = DH(`beacon_prekey_sk`, `server_ephemeral_pk`)
  - dh4 = DH(`beacon_onetime_sk`, `server_ephemeral_pk`)
- Compute the derived secret `KDF(Padding || DH1 || DH2 || DH3 || DH4 || SS)` using the PQXDH protocol string as HKDF `info`
  - `Padding` is 32 `0xFF` bytes
- Delete its one-time keypair.
- Save the server's public key
- Save its own key ID using the `keyId` field
- Create the associated data byte string by concatenating the encoded server identity key, encoded beacon identity key and the PQXDH and symmetric ratchet protocol strings
- Initialize its side of the ratchets using the derived secret with the symmetric ratchet protocol string as HKDF `info`
- Decrypt the `appCipherText` as a `CryproFrame`, using its `recv` keychain
- If decryption is successful, return the plaintext to the caller oherwise abort the protocol and delete the previously derived cryptographic state

# Protocol details
Once the session has been created, meaning a successful PQXDH run, the associated data (`AD`) is created. This is made up of the concatenation of the public keys of both parties, the key exchange protocol string and the ratchet protocol string. This associated data is used in every encryption for a given `(Server, Beacon)` tuple. It is then expected that beacons will read messages from the server from their transport protocol and hand them off to beaconcrypt immediately for decryption and deserialization. All encrypted buffers (`CryptoFrame`s) carry a sequence number `seq` and a direction flag `sToB`. These are used to handle out-of-order messages and protect against replay attempts, and therefore need to be protected. Thus, there is an outer layer which uses signatures to ensure the `CryptoFrame` are not modified in transit. This layer itself needs to identify the key pair used to sign the message. This is accomplished using a `keyId`. This signature layer is not mandatory, callers are given the choice whether to created signed messages or not. However, I do recommmend opting into it as it's very cheap and protects the critical `seq` field.
