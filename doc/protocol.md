<!-- SPDX-License-Identifier: 0BSD -->

# Overview
The protocol uses signal's `PQXDH` for key establishment alongside a symmetric ratchet to generate message keys. Every encryption uses a new key derived from the ratchet using an AEAD scheme. It is implemented on top of `libsodium`. The interface provides opaque byte strings that either party can put on the wire. The intent is to provide a generic cryptographic layer, upon which you can use whatever your beacon speaks. Unfortunately, Mythic requires some bookeeping information (a UUID) to be prepended to any message, so that will have to be added regardless and will not be protected. I don't know enough about sliver, CS, havoc or any other framework to say anything about them.

## Assumptions
It is assumed that the server's identity public key and numeric server identity-key ID are pinned in the beacon. Applications that persist or replicate server state must use a trusted store that protects snapshot integrity and provenance, provides durable linearizable compare-and-swap, and maintains a rollback-resistant authoritative head. Snapshots contain plaintext secrets and are not self-authenticating.

## Motivation for dropping certain properties
The signal protocol, which is to say `PQXDH` + `triple ratchet`, is proven to provide two important properties: Forward Security (`FS`), and Post-Compromise Security (`PCS`). The former means that an attacker cannot learn how to decrypt previous messages by compromising a participant in beaconcrypt at a given point in time. The latter means that an attacker cannot learn how to decrypt future messages by compromising a participant in beaconcrypt at a given point in time. In the context of a C2 protocol, `PCS` seems unnecessary. Indeed, if an attacker can access the current cryptographic state of the application, one of two things has happened. First, they have compromised our beacon. At this point, the attacker can either run whatever they want themselves, or through our beacon and we have failed at preventing the attacker from injecting arbitrary commands. However, the attacker cannot read past messages because of `FS`, so the confidentiality of data that was previously exfiltrated is preserved provided they cannot just access it themselves. In the second case, the attacker has compromised the C2 server. This is game over with any C2 server I'm aware of, as at this point the attacker has access to all the data that was exfiltrated and can task any beacon the server knows about. It is this analysis that leads to `PCS` being dropped from the requirements for this protocol, while `FS` remains desirable. Another point is that `triple ratchet`, the PQ Continuous Key Agreement (`CKA`) mechanism used by signal is quite complicated and requires a lot of state management, which just smells like logic bugs to me.

Additionally, the signal protocol also provides something called `message commitment`. Authenticated encryption with associated data (AEAD) has the property that two plaintexts encrypted under two different keys can generate the same ciphertext and authentication tag. This may allow an attacker to exploit a confused deputy to get one principal to obtain a different message than other participants. This attack is often called `invisible salamanders`. Beaconcrypt provides strong commitment, that is to say it commits to the key, nonce, associated data, sender id, encryption key sequence number and message through the use of [Chan and Rogaway's `CTX` scheme](https://eprint.iacr.org/2022/1260). The `CTX` scheme is slightly modified, in that beaconcrypt still transmits the original AEAD tag alonside the `CTX` tag. This is done to remain compatible with the public libsodium interface.

The deterministic ChaCha20-Poly1305 multi-opening fixture used to test this property, including its Poly1305 derivation and independent verification procedure, is documented in [multi-opening-fixture.md](multi-opening-fixture.md).

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

The beacon receives the initial message and uses the `phase2` bundle to perform the final leg of the `PQXDH` protocol run. It uses the shared secret to initialize its KDF chains, then attempts to decrypt the bundled ciphertext using its receive chain. The session is established only if decryption succeeds, the implicit sequence is 1, the commitment uses the pinned Server ID, and the first eight plaintext bytes equal the outer response’s claimed `keyId` in little-endian form followed by nonempty application plaintext. A response encrypted under another sequence or sender context fails authentication. Established sessions retain the general receive path and its out-of-order delivery rules. At runtime the beacon's operational ratchet is owned only by `BeaconState::Established`, and the server peer map contains only `EstablishedRemote` entries produced by a successful registration commit or fresh restoration through the trusted store. Fresh, pending, and aborted beacon states cannot encrypt or decrypt application records, and the production API does not expose manual peer insertion, ratchet reset, or mutable ratchet access.

# Message encryption
Established-session encryption wraps its payload in a CBOR message called a `CryptoFrame`, whose metadata supports out-of-order delivery. An established sender derives a key, next chain, and nonce from its current send chain, advances its operational ratchet, and consumes the message key even if encryption fails. The operational ratchet and its secret-bearing chain/material components are not `Clone`, and update APIs return an inert serialized `RatchetSnapshot` rather than another live manager. These ownership controls prevent safe in-process state forks. Restart and multi-owner safety depend on the trusted-store generation/digest/CAS persistence path; key and nonce uniqueness additionally require correct HKDF execution and noncollision of the derived values. Send material is removed logically after the attempt and core arrays use best-effort zeroization on drop, but physical erasure cannot be guaranteed. Receive material is retained only for bounded out-of-order delivery after a successful future receive; every normally rejected receive preserves the complete entry state, while successful authentication consumes the selected record and later replay fails. The commitment described below binds `seq` and `keyId` to the protected payload, with `seq` selecting the derivation position and `keyId` identifying the sender and selected receive ratchet.

## State ownership and persistence

The ordinary `Server` API is an affine, volatile in-memory owner: it is not clonable and exposes neither full-state restoration nor mutable operational ratchets. Deployments that must persist, restart, fail over, or coordinate workers use `PersistentServer`. Its plaintext `ServerSnapshot` envelope carries a lineage, generation, parent digest, version, kind, and canonical server-state payload, but no authentication tag or encryption. `PersistentServer::restore` validates and decodes the current snapshot loaded from the trusted store, verifies canonical re-encoding, and advances the generation by compare-and-swap before making the restored server operational. Every state-changing wrapper withholds its result until the successor snapshot is durably committed; a failed CAS poisons that local owner so it cannot continue as a fork. The `SnapshotStore` implementation is part of the security boundary and is trusted for snapshot integrity and provenance; it must atomically compare the complete trusted head, durably store the replacement, return only the authoritative current snapshot, and keep its state in a rollback-resistant domain. The unkeyed digest links complete records but does not authenticate bytes obtained elsewhere. See [State persistence](persistence.md) for the complete contract.

## Commitment
Beaconcrypt uses a commitment scheme based on [`CTX` by Chan and Rogaway](https://eprint.iacr.org/2022/1260). This intends to both provide protection against key substitution attacks and protect metadata. However, because of this additional metadata being included in the `CTX` transcript, it might be susceptible to canonicalization attacks. Therefore, it is critical that all elements included in the `CTX` transcript be of fixed size, such that no confusion is possible. For the reference `beaconcrypt` implementation these are:
```
-----------------------------------------------------
| ChaCha20-Poly1305 IETF Key (K) - 32 bytes         |
-----------------------------------------------------
| ChaCha20-Poly1305 IETF Nonce (N) - 12 bytes       |
-----------------------------------------------------
| Beaconcrypt PQXDH associated data (A) - 153 bytes |
-----------------------------------------------------
| ChaCha20-Poly1305 IETF Tag (T) - 16 bytes         |
-----------------------------------------------------
| Seq for K as little-endian (S) - 8 bytes          |
-----------------------------------------------------
| Principal ID as little-endian (I) - 8 bytes       |
-----------------------------------------------------
```

The commitment itself, which is 64 bytes, is then computed using the following, where `H` is the unkeyed BLAKE2b hash function with 512 bits of output:
```
H(K, N, A, T, S, I)
```

A canonicalization scheme would have to be used to encode the various elements being included within the `CTX` transcript if the fixed-size assumption were to become false.

## Ratchet initialization
Beaconcrypt uses a symmetric ratchet protocol for CKA. This provides forward, but not post-compromise, secrecy. There are two ratchets, one for encrypting messages to be sent (`send`), and one for decrypting received messages (`recv`). Both ratchets are initialized from a single 256 bit secret value derived from the `PQXDH` protocol run. Because of the `send`/`recv` division, the server and beacon have a slightly different initialization routine:
```
RM = KDF(DS, info)
LHS = RM[0..31]
RHS = RM[32..63]

// beacon side
RK = LHS
SK = RHS
// server side
RK = RHS
SK = LHS
```
Where:
 - `KDF` is HKDF-SHA-512(IKM, INFO) with no salt and 64 bytes of output
 - `DS` is the `PQXDH` derived secret
 - `info` is the `SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305` string as utf8 bytes
 - `RK` is the initial state of the `recv` key chain
 - `SK` is the initial state of the `send` key chain

## Ratcheting
The `send` and `recv` key chain are ratcheted foward on every encryption and decryption operation, respectively. The ratchet output is used to generate three things: the new state of the key chain, the message key, and the message nonce:
```
O = KDF(KCS, info)
K = O[..31]
S = [32..63]
N = [64..75]
```
Where:
 - `KDF` is HKDF-SHA-512(IKM, INFO) with no salt and 76 bytes of output
 - `KCS` is current state of the chain being ratcheted
 - `info` is the `SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305` string as utf8 bytes
 - `K` is the message key
 - `S` is the new state of the ratchet
 - `N` is the message nonce

Initial ratchet expansion uses the same symmetric-ratchet label and input convention with a 64-byte output, so for an equal input it is the first 64 bytes of the 76-byte record-step stream; output length is not domain separation.

# Protocol message

## Wire encoding

Messages use exact deterministic CBOR arrays from [transport.cddl](../beaconcrypt-parse/schema/transport.cddl); keys and ciphertexts are byte strings, and numeric fields are unsigned 64-bit integers. Decoders require complete input and reject unknown versions/kinds, extra fields, nonminimal encodings, and indefinite values.

| Message | CBOR array |
| --- | --- |
| `InitKex` | `[1, 0, identityKey, preKey, oneTimeKey, pqKey]` |
| `KexResponse` | `[1, 1, identityKey, ephemeralKey, kemCipherText, appCipherText, keyId]` |
| `CryptoFrame` | `[1, 2, seq, keyId, cipherText]` |

The inclusive limit is **32 MiB (33,554,432 bytes) per complete encoded message**, including every header, authentication tag, and commitment. Exact size checks reject oversized sends before output allocation or ratchet advancement; they do not cap plaintext snapshots or JSON state. This replaces the former Cap'n Proto wire format without fallback; peers and queued messages must use CBOR. Fixed-width LE64 commitment inputs and snapshot formats are unchanged.

## CryptoFrame
This is the most basic framing for an encrypted message within beaconcrypt. It is defined in [transport.cddl](../beaconcrypt-parse/schema/transport.cddl). It carries a key identifier (`seq`), a key identifier `keyId`, and the encrypted data under `cipherText`. These messages are closely tied to the ratcheting mechanism. To create such a message, the writer must:
- Reject a complete encoded frame above the message limit before ratcheting
- Ratchet their `send` keychain forward and get the sequence number `key_seq`
- Use their current `send` key to encrypt the message into a pair of temporary variables `CT` and `T` 
- Compute the commitment `T*` using `Hash(Key, Nonce, Associated Data, T, key_seq, key_id)`
  - The hash function is unkeyed Blake2b with a 512bit output length
  - `key_seq` and `key_id` are serialized as little-endian 64-bit unsigned integers
  - `key_id` is the principal's public key identifier
- Append `T` and `T*` to `CT` and place the resulting buffer in `cipherText`
- Set `seq` to `key_seq`
- Set `keyId` to `key_id`
- Delete the current `send` key

To read a `CryptoFrame`, the reader must:
- Reject an empty, oversized, unparsable, or too-short frame before changing ratchet state
- Use `keyId` to select the sender's identity, associated data, and receive ratchet
- Reject sequence zero and any old sequence whose cached key has already been consumed
- Check that a future `seq` is admissible under both receive limits
  - Let `skipped = seq - current_receive_sequence - 1`; the target itself is consumed separately
  - The reference implementation permits at most 50 skipped keys, allowing up to 51 derivations including the target
  - The number of already cached receive keys plus `skipped` must also be at most 50
  - Abort processing without changing state if either limit is exceeded
- Privately prepare the candidate receive transition without changing the live receive chain, counter, or cache
  - For a future `seq`, derive the bounded candidate chain and material while staging only the skipped keys; keep the target material separate
  - For an old `seq`, select the exact sequence-tagged cached key without removing or moving it
- Extract `CT`, `T` and `T*` from the `cipherText` field
- Compute the commitment `T*'` using `Hash(Key, Nonce, Associated Data, T, seq, keyId)`
  - The hash function is unkeyed Blake2b with a 512bit output length
  - `seq` and `keyId` are serialized as little-endian 64-bit unsigned integers
- Perform a constant-time comparison of `T*` and `T*'`
  - Reject the frame with the complete entry state unchanged if there is a mismatch
- Use the privately selected key associated with `seq` to decrypt
  - Reject the frame with the complete entry state unchanged if AEAD authentication fails
- Publish the prepared receive chain, counter, and skipped keys only after successful authentication, and consume rather than cache the target key

State-neutral rejection prevents unauthenticated traffic from consuming receive-cache capacity, but it trades that protection for bounded recomputation: retrying the same invalid future frame can repeat up to 51 private ratchet-KDF steps—50 skipped-key derivations plus the separately consumed target. Deployments should apply per-peer rate limits, admission quotas, or transport replay filtering as external availability controls; those controls must not encode rejection by mutating the cryptographic ratchet.

## InitKex
This message starts the beacon registration process by initiating the `PQXDH` protocol run. It is defined in [transport.cddl](../beaconcrypt-parse/schema/transport.cddl). It must only be run once per beacon instance. The beacon must generate all relevant cryptographic keys using the appropriate libsodium API before trying to construct this message. Ed25519 and ML-KEM-768 public keys are encoded as a one-byte type marker followed by the public-key buffer. The two X25519 fields additionally authenticate their semantic role and are encoded as `[type: u8, role: u8, key]`: `preKey` is `[0x04, 0x80, 32-byte key]` and `oneTimeKey` is `[0x04, 0x81, 32-byte key]`. Type markers occupy the low half of the byte domain and role markers the high half, so the domains are disjoint. The beacon builds this message as follows:
- Set `identityKey` to the beacon's Ed25519 encoded identity public key
- Set `preKey` to the complete type-and-prekey-role encoded X25519 public key signed under the beacon's identity key
- Set `oneTimeKey` to the complete type-and-one-time-role encoded X25519 public key signed under the beacon's identity key
- Set `pqKey` to the beacon's ML-KEM-768 encoded ML-KEM public key signed under the beacon's identity key

Beaconcrypt assumes the use of the libsodium `sign` API for all signatures. In this scheme, the signature is prepended to the buffer, so there are no dedicated signature fields.

The signed X25519 payloads are now 34 bytes and are intentionally incompatible with the former 33-byte encodings that did not distinguish prekeys from one-time keys. A live Beacon emits its registration bundle at most once, and any failure while completing registration permanently aborts that Beacon object.

The server must use this message as follows:
- Verify that all keys except `identityKey` are signed under `identityKey`
- Reject an X25519 field unless both its type marker and its field-specific role marker match; exchanging or duplicating the two valid signed fields is invalid
- Construct the 64-byte registration identifier as the decoded beacon identity public key followed by the decoded signed one-time X25519 public key
- Reject the message if that exact identifier is already in the server's consumed-registration set
- Generate its ephemeral X25519 keypair
- Encapsulate the PQ shared secret (`SS`) using `pqKey`
- Convert the beacon's identity public key and the server's identity secret key to X25519 format using libsodium's `ed25519_pk_to_curve25519` and `ed25519_sk_to_curve25519` respectively (thereafter they will use the `_kex` suffix)
- Perform the 4 Diffie Hellman rounds
  - dh1 = DH(`server_id_sk_kex`, `beacon_prekey_pk`)
  - dh2 = DH(`ephemeral_sk`, `beacon_id_pk_kex`)
  - dh3 = DH(`ephemeral_sk`, `beacon_prekey_pk`)
  - dh4 = DH(`ephemeral_sk`, `beacon_onetime_pk`)
- Compute the derived secret `KDF(Padding || DH1 || DH2 || DH3 || DH4 || SS)` using the exact 46-byte HKDF `info` string `BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768`
  - `Padding` is 32 `0xFF` bytes
- Delete all Diffie Hellman output
- Add the registration identifier to the consumed set before returning the pending response material; this is permanent even if response construction later fails
- Return the KEM ciphertext, derived secret, ephemeral public key and beacon public key

## KexResponse
This message enables the beacon to obtain the elements it needs to derive the shared secret. It is defined in [transport.cddl](../beaconcrypt-parse/schema/transport.cddl). It is intrinsically linked to the corresponding `InitKex` which intiated the protocol run. It is expected that the server will create this message immediately after parsing a valid `InitKex`. It also potentially carries the first of the server's messages to the beacon. The server must contruct it as follows:
- Create a new key ID to assign to the beacon using checked increment; abort if the counter is exhausted or the exact next ID is already occupied
- Stage a new known cryptographic identity using the beacon's public key and newly created key ID without publishing it yet
- Initialize its side of the ratchets using the derived secret with the exact 41-byte HKDF `info` string `SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305`
- Delete the derived secret
- Set the `keyId` field to the newly generate beacon's key ID
- Set the `ephemeralKey` field to the X25519 ephemeral public key from the corresponding `InitKex`
- Set the `identityKey` to the server's Ed25519 public key
- Set the `kemCipherText` to the KEM ciphertext from the corresponding `InitKex`
- Create the associated data byte string by concatenating the encoded server identity key, encoded beacon identity key, `BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768`, and `SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305`
- Encode the assigned beacon key ID as an eight-byte little-endian value and prepend it to the first message, or to a single `0xFF` byte when no message was supplied
- Set `appCipherText` directly to the encrypted `ciphertext || tag || commitment`, without a nested CBOR frame
- Use implicit sequence `1` and the pinned numeric server identity-key ID as commitment inputs
- Delete the ephemeral key pair
- After encryption and serialization succeed, atomically commit the key-ID counter, staged peer identity, and ratchets
- Return the serialized registration response and key ID to the caller

Upon reception, the beacon must process this message as follows:
- Check that `identityKey` contains the same key as the compiled-in server key
  - Abort in case of mismatch
- Decapsulate the shared PQ secret using `kemCipherText` adn the beacon's KEM secret key
- Convert the beacon's identity secret key and the server's identity public key from `identityKey` to X25519 format using libsodium's `ed25519_sk_to_curve25519` and `ed25519_pk_to_curve25519` respectively (thereafter they will use the `_kex` suffix)
- Compute the 4 Diffie Hellman rounds
  - dh1 = DH(`beacon_prekey_sk`, `server_id_pk_kex`)
  - dh2 = DH(`beacon_id_sk_kex`, `server_ephemeral_pk`)
  - dh3 = DH(`beacon_prekey_sk`, `server_ephemeral_pk`)
  - dh4 = DH(`beacon_onetime_sk`, `server_ephemeral_pk`)
- Compute the derived secret `KDF(Padding || DH1 || DH2 || DH3 || DH4 || SS)` using the exact 46-byte HKDF `info` string `BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768`
  - `Padding` is 32 `0xFF` bytes
- Delete its one-time keypair.
- Delete its PQ keypair
- Delete all Diffie Hellman output
- Treat `keyId` as the proposed assigned identity, without publishing it yet
- Create the associated data byte string by concatenating the encoded server identity key, encoded beacon identity key, `BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768`, and `SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305`
- Initialize its side of the ratchets using the derived secret with the exact 41-byte HKDF `info` string `SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305`
- Delete the derived secret
- Authenticate and decrypt raw `appCipherText` using the initial `recv` keychain, implicit sequence `1`, and pinned numeric server identity-key ID; otherwise abort registration and discard the staged ratchet
- Split the authenticated plaintext into its eight-byte prefix and remaining application plaintext, and require the prefix to equal the little-endian encoding of `keyId`
- Commit the assigned identity and staged ratchets only after that check passes
- Strip the prefix before returning the application plaintext
- If decryption is successful, return the plaintext to the caller oherwise abort the protocol and delete the previously derived cryptographic state

# Protocol details
Once the session has been created, meaning a successful PQXDH run, the 153-byte associated data (`AD`) is the server's `0x01 || Ed25519 public key`, the beacon's `0x01 || Ed25519 public key`, the 46-byte PQXDH label, and the 41-byte symmetric-ratchet label in exactly that order. Authenticated bundle fields encode an ML-KEM-768 public key as `0x03 || pk`, an X25519 prekey as `0x04 || 0x80 || pk`, and an X25519 one-time key as `0x04 || 0x81 || pk`, so algorithm and X25519 role encodings are disjoint. This associated data is used in every encryption for a given `(Server, Beacon)` tuple. It is then expected that beacons will read messages from the server from their transport protocol and hand them off to beaconcrypt immediately for decryption and deserialization. All encrypted buffers (`CryptoFrame`s) carry a sequence number `seq` and sender identity `keyId`; neither field is part of the base AEAD associated data, and the protocol adds no AEAD or CTX domain label. The unlabeled CTX commitment binds both fields, encoded separately as LE64 values after the retained AEAD tag, to the ciphertext, so modifying either field causes decryption to fail.

The `KexResponse.keyId` field claims the receiving beacon’s assigned routing ID; the response payload has no inner frame, and authenticates implicit sequence `1` plus the pinned numeric server ID. The Server prepends the assigned ID to its initial registration plaintext. Later application plaintext has no automatic recipient prefix. This does not change the 153-byte long-lived associated data or CTX commitment layout used for subsequent records.
