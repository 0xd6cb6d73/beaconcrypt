<!-- SPDX-License-Identifier: 0BSD -->

# Reviewed formal-verification trust boundary

This is the canonical Stage 9 inventory for the beaconcrypt proof boundary.
It records the production behavior that remains opaque to extraction, the laws
used to relate that behavior to the proofs, the adapter refinements required by
the theorems, the trusted proof-library surface, generated-backend exceptions,
and every repository-owned handwritten backend review unit.

The accompanying `reviewed-inventory.txt` fingerprints the files that realize
this inventory. `make check-inventory` checks those fingerprints, derives the
complete handwritten/generated file sets, and checks the structural exception
counts below. A changed fingerprint is a review tripwire: it forces an
intentional manifest change into the same review, but it cannot establish that
a human performed a sound review.

## Boundary baseline

The reviewed baseline has:

- no `hax_lib::opaque` or `hax_lib::opaque_type` annotation in the protocol
  core;
- three generated F* modules and three strictly checked handwritten F* lemma modules;
- one generated ProVerif library, exactly three production-backed replacement fragments, eleven handwritten ProVerif model/query libraries, and six top-level process files;
- no local F* `assume` or `admit`, no lax checking, and no unresolved generated
  backend placeholder; and
- one handwritten ProVerif result classifier that is trusted to distinguish
  required positive results, reachability witnesses, and deliberate negative
  compromise results.

The core owns deterministic protocol decisions. Cap'n Proto, serde,
libsodium, ML-KEM, allocation, entropy, persistence mechanics, erasure, and
language bindings remain outside extraction.

## Opaque Rust and adapter functions

The entries below are the repository-owned production wrappers in the claimed
high-level trace. The named external calls are opaque: neither hax backend
extracts their Rust implementation.

| ID | Production review unit | Opaque behavior and proof relevance |
| --- | --- | --- |
| OR-01 | `<BeaconCryptPqxdh as CryptoProvider>::{new,default}` | Initializes libsodium; generates an Ed25519 identity or derives the server identity from a supplied seed; validates the beacon's configured server Ed25519 key; constructs the proof-visible `ServerBinding` from that exact public key and numeric identity-key ID; and, for a configured beacon, generates its X25519 prekey and ML-KEM keypair. A beacon without a configured server key enters terminal aborted state. `ensure_init`, `crypto_sign::KeyPair::{generate,from_seed}`, `crypto_kx::KeyPair::generate`, and `crypto_kem::mlkem768::KeyPair::generate` are outside the proof. Persistence restoration is OR-14, not part of `new`. |
| OR-02 | `<BeaconCryptPqxdh as ProviderBeacon>::get_registration_bundle`, `new_onetime_keypair`, `delete_onetime_keypair`, `delete_pq_keypair`, and `abort_registration` | Supplies fresh one-time coins, maps the core `InitKex` fields to Cap'n Proto, signs the complete role-tagged X25519 and typed ML-KEM payloads with `crypto_sign::sign`, and performs the consuming or terminal production phase change. The public deletion helpers are compatibility/abort paths, not additional successful traces. |
| OR-03 | `<BeaconCryptPqxdh as ProviderBeacon>::finish_registration` | Parses the response, passes its Ed25519 identity to the core comparison against the binding retained from construction, converts that response key to X25519, decapsulates ML-KEM, computes ordered DH1--DH4, derives the root and initial chains, opens the first record using the retained numeric server ID, passes the successfully opened sender ID and assigned-ID prefix to the core authentication transition, checks the concrete peer-map entry still equals the retained binding, and publishes the staged ratchet. It does not obtain the expected public key from a finish-time map lookup. |
| OR-04 | `<BeaconCryptPqxdh as ProviderServer>::get_shared_secret` | Parses `InitKex`, calls `crypto_sign::verify` three times, validates role tags, classifies and consumes the semantic replay ID, creates ephemeral/KEM coins, performs the complementary four DH operations, and derives the root. |
| OR-05 | `<BeaconCryptPqxdh as ProviderServer>::build_registration_response` | Refines key-ID availability, initializes the complementary ratchet, seals the authenticated assigned-ID prefix, and serializes the response. Every recoverable `None`/`?` failure occurs before the final no-failure commit section, which then publishes the peer/ratchet and server counter sequentially as one logical transition; crash, panic, and concurrency atomicity are not claimed. |
| OR-06 | `shared_secrets` and `derive_root_key_input` in `src/pqxdh.rs` | Translate the five concrete shared secrets without reordering and call `crypto_kdf::hkdf::sha512::{extract,expand}` with `PQXDH_INFO`; the transcript is erased after the call. The test-only `derive_root_key` uses the same wrappers. |
| OR-07 | `<Ratchet<Role> as Ratchetable>::ratchet` and `<KdfOutput<Role> as From<[u8; 76]>>::from` | Call HKDF-SHA-512 once for one admitted logical step, split its output into a 32-byte key, 32-byte next chain state, and 12-byte nonce, and erase the temporary output. |
| OR-08 | `RatchetManager::init_ratchets` | Calls HKDF-SHA-512 with `SYM_RATCHET_INFO`, requires exactly two 32-byte halves, applies the core-provided role offsets, and publishes both concrete chain states together. |
| OR-09 | `CryptoProvider::encrypt_message`, `encrypt_message_with_ratchet`, and `<BeaconCryptPqxdh as ProviderServer>::{encrypt_and_update,encrypt_and_update_json}` | The trait method selects one target peer and associated data. The helper obtains one core send capability and concrete key, calls ChaCha20-Poly1305 `encrypt_detached`, builds the CTX commitment, serializes the frame, and consumes the key on every outcome after allocation. The update wrappers snapshot or JSON-serialize the resulting state. |
| OR-10 | `CryptoProvider::decrypt_message`, `encrypted_frame_sender`, `decrypt_message_with_ratchet`, and `<BeaconCryptPqxdh as ProviderServer>::{decrypt_and_update,decrypt_and_update_json}` | The trait method parses the sender ID and selects its peer/associated data. The helper rejects empty, unparsable, wrong-sender, and too-short frames before receive admission; an admitted future frame then performs exactly the planned KDF steps before commitment/AEAD authentication and retains that complete post-admission state and candidate key on failure. Success consumes only the candidate key. The update wrappers snapshot or JSON-serialize the resulting state. |
| OR-11 | `build_commitment` | Checks/converts the concrete slices, passes `(key, nonce, associated data, AEAD tag, sequence, sender ID)` to the extracted core `build_commitment_transcript`, and calls libsodium BLAKE2b `crypto_generichash::generichash` over the returned 229 bytes. F* proves the helper's exact fixed-width order and both LE64 encodings; slice provenance, conversion, the opaque hash call, and compiled caller remain adapter obligations. `libsodium_rs::utils::memcmp` performs concrete secret/commitment comparison. |
| OR-12 | `RatchetManager::{default,ratchet_send,send_key,recv_key,ratchet_recv,ratchet_recv_until,consume_send_key,complete_recv_key,receive_key_slot,send_cache_matches_control,receive_cache_matches_control,reset,restored_send_capability}` and the same-named `CryptoProvider` delegation helpers | Pair concrete send-map keys with core capabilities, store concrete receive keys in the physical slots assigned by the core fixed array, mirror its swap removal, derive exactly the admitted number of keys, refine completion to the core disposition, and reconstruct the logical/concrete relation. The public `delete_send_key`/`delete_recv_key` wrappers route to the same completion functions; direct low-level use remains outside the claimed high-level trace. |
| OR-13 | `<BeaconCryptPqxdh as CryptoProvider>::{associated_data,ratchet_manager,ratchet_manager_mut,identity_key_kid,server_id,pk_by_kid,identity_pk,identity_sk,pq_pk,pq_sk}`, `RemotePrincipal::{new,pk,ratchet,ratchet_mut}`, and the peer-map mutators/accessors in those impls | Refine unique `HashMap` peer selection, role-specific key access, and unchanged non-selected peers to the pointwise core transition. Compatibility setters, reset, and manual peer mutation are outside the claimed trace even though the entire impl is fingerprinted. |
| OR-14 | `<BeaconCryptPqxdh as ProviderServer>::{export_state,try_from_state}`, `ProviderServer::from_state`, `RatchetManager` serialization/deserialization, `serialize_server_state`, `deserialize_server_state`, and the complete serde impl blocks in `src/ser.rs`/`src/deser.rs` | Serde/JSON persistence is not extracted. Import validates typed key roles, sequence/counter bounds and cache capacity; materializes map entries, sorts receive indices, and reconstructs control only through the restore API; and validates replay-history shape plus server/peer ID bounds. Duplicate raw JSON keys are not claimed to be rejected before ordinary `HashMap` deserialization. The JSON update methods additionally use the `StateUpdate` serde impl. |
| OR-15 | `zeroize_shared_secrets`, `<SecretArr as From<Vec<u8>>>`, `<SecretArr as From<[u8; S]>>`, `SecretArr::{as_slice,copy_from_slice,inner}`, `Zeroize::zeroize`, and `Zeroizing` uses | Fixed-length conversions connect opaque primitive bytes to core inputs. Best-effort physical erasure is implementation behavior, not a theorem premise or conclusion; the proof claims only logical unavailability after the relevant state transition. |
| OR-16 | `encode_sign`, `decode_sign`, Cap'n Proto readers/builders inside OR-02--OR-05, and `build_associated_data` | Validate or construct typed persistence/wire bytes and map them to the exact proof-visible fields. These conversions are adapter obligations, not cryptographic authentication by themselves. The `#[cfg(test)]`-only `encode_kem`/`decode_kem` helpers are monitored with their source file but are not production review units. |
| OR-17 | `memset_explicit`, the Windows-GNU `SystemFunction036` shim, and its external `BCryptGenRandom` call | Supply platform erasure/RNG compatibility below the primitive boundary. Their implementation, constant-time behavior, and OS entropy are outside the proof. |
| OR-18 | Every other function in `build.rs` and the complete `src/{beacon,cbinds,deser,error,lib,pqxdh,pybinds,ser,server,shared}.rs` adapter set | The recursively checked whole-file review units classify all remaining schema generation, bindings, API forwarding, formatting, tests, and compatibility/direct low-level functions as outside the proof claim. This is the exhaustive catch-all for repository-owned Rust outside the isolated core, not an assertion that those functions are verified. |

The external primitives covered by these wrappers are Ed25519 signing and
verification, Ed25519-to-X25519 public/secret conversion, X25519 scalar
multiplication, ML-KEM-768 encapsulation/decapsulation, HKDF-SHA-512,
ChaCha20-Poly1305-IETF, BLAKE2b, OS-backed key generation, constant-time byte
comparison, Cap'n Proto parsing/serialization, serde, allocation, and
zeroization. Byte constructors such as `from_bytes` are wire-validation
operations, not evidence that the wire is authenticated.

For opacity accounting, there are zero explicit hax-opaque functions in the
isolated core. Every repository-owned function outside that core is opaque to
extraction and is covered by the recursively derived, whole-file
`adapter-rust` manifest. OR-01--OR-17 name the proof-relevant functions and
complete impl blocks within the claimed trace; OR-18 exhaustively classifies
every other function by its whole-file review unit. Changing any of them still
trips the conservative file-level review baseline.

## Assumed primitive laws

The F* modules do not declare these as local axioms. Their honest-run results
are conditional on adapter inputs satisfying the relevant relations. The
ProVerif model represents the same boundary with ideal symbolic constructors
and the six reductions in `crypto.pvl`, which is stronger than a computational
claim and is stated explicitly here.

| ID | Reviewed law |
| --- | --- |
| PL-01 | Key-generation coins used for distinct honest identities, one-time keys, ephemeral keys, KEM encapsulations, and sessions are fresh. Seeded identity generation is deterministic for the supplied seed. RNG implementation security is not proved. |
| PL-02 | An honestly generated Ed25519 signature verifies to the exact signed message under the matching public key; successful verification used as authentication has the usual symbolic unforgeability/provenance meaning. No equation verifies a signature under a different key or for a different message. |
| PL-03 | Ed25519 public- and secret-key conversion name the same X25519 identity secret for the honest pair. Invalid encodings/conversions are rejected by the adapter. |
| PL-04 | Each complementary X25519 pair computes the same DH value. All-zero outputs are rejected by the core before root construction. General X25519 arithmetic and contributory behavior are not proved. |
| PL-05 | ML-KEM encapsulation and decapsulation with the matching public/secret key pair and ciphertext produce the same shared secret. ML-KEM's implementation and computational security are not proved. |
| PL-06 | HKDF is deterministic for identical input and label. Production uses `PQXDH_INFO` for root extraction/expansion and `SYM_RATCHET_INFO` both for initial two-chain derivation and each later chain step; state inputs and fixed output offsets distinguish those production uses. ProVerif uses stronger, separate ideal root/chain/material constructors and idealizes their collision freedom. Output splitting is an adapter refinement, not an HKDF law. |
| PL-07 | For a fixed key, nonce, associated data, and ciphertext/tag, ChaCha20-Poly1305 decryption is deterministic and inverts an honest seal. Authenticity under the intended honest key/context supplies the record-provenance assumption, but does not forbid the same ciphertext/tag from opening under another adversarially selected key/context. The ordinary symbolic record rule is stronger and exact-opening; the separate weak-AEAD negative control deliberately permits two distinct openings so that rule is not used as evidence for CTX's added benefit. |
| PL-08 | F* proves that the extracted fixed-size CTX input is injective over all six fields and that, for arbitrary pure 229-to-64-byte hash and AEAD-open functions, two semantically distinct accepted explanations of one fixed `C || T || U` payload return an explicit witness containing unequal production transcripts with equal hash outputs. The AEAD-open function may multi-open across unequal keys or contexts; only same-input determinism is used. Instantiating the abstract hash with BLAKE2b-512 gives the conventional commitment-to-collision advantage lifting, while BLAKE2b collision resistance, probability/runtime accounting, the opaque production hash wrapper, and compiler correspondence remain assumptions or unproved obligations. ProVerif separately idealizes the commitment as a collision-free constructor and checks one explicit CTX/no-CTX weak-AEAD differential control. |
| PL-09 | The symbolic type/role tags, registration identifier, ordered root input, associated data, and key-ID encoding are injective/disjoint constructors for the fixed layouts proved by F*. The generated `build_associated_data` replacement is an ideal data constructor for that proved layout. |
| PL-10 | ProVerif's fresh assigned-key-ID names and constructor-generated `first_sequence`/`next_sequence` terms model only checked, non-exhausted, collision-free bounded prefixes of the production `u64` spaces. The failed-receive process explicitly unrolls one exact 50-slot cache execution but does not prove arbitrary gaps, cache arrangements, finite-counter executions, or wraparound behavior; those control facts are covered by F*. |
| PL-11 | For equal-length byte slices, production `libsodium_rs::utils::memcmp` returns true exactly when every byte is equal. Its constant-time implementation is not proved. The receive trace relies on this law for the computed-versus-wire CTX commitment; the other repository use additionally compares `SecretArr` system/role `TypeId`s and is not reached by the claimed trace. |

## Adapter refinements and trace preconditions

These statements connect concrete production state to the extracted logical
state. They are obligations of the adapter and its regression tests, not
conclusions obtained merely by typechecking the core extraction.

| ID | Required refinement or precondition |
| --- | --- |
| AR-01 | Each physical `recv_past` slot below `RatchetState::receive_cache_len` contains exactly the concrete key for the logical sequence in the same core slot; all later slots are empty, and capacity is 50. |
| AR-02 | Each successful `advance_receive` causes exactly one concrete HKDF step and associates its result with the returned sequence and slot. Rejected admission is state-neutral, but admitted future derivation occurs before frame authentication and is retained if authentication fails. |
| AR-03 | Each successful `advance_send` is paired with exactly one concrete key and logical capability. Both are removed/finished after the one permitted encryption attempt, including an AEAD or serialization failure. |
| AR-04 | Failed receive authentication retains the complete post-admission logical/concrete state, including every newly derived skipped key and the exact candidate key. Repeating that failed target derives nothing further. Success removes exactly that target from both representations, so replay cannot find it and the freed slot is available to a later admitted receive. |
| AR-05 | High-level peer lookup selects one unique map entry matching the authenticated sender/target ID and leaves every other peer unchanged. Low-level mutators, cloned pending send capabilities, state forks, and rollback are excluded. |
| AR-06 | Persistence import checks sequence bounds, materializes send/receive maps, sorts receive indices, and rebuilds only through `start_restore`/`restore_receive_key`/`finish_restore`, rejecting oversized or structurally invalid logical state. Duplicate raw JSON map keys may be resolved by ordinary serde `HashMap` parsing before these checks. Persistence confidentiality, storage atomicity, and rollback prevention remain external. |
| AR-07 | Cap'n Proto Phase 1 fields translate exactly to the core's tagged identity, role-tagged prekey, role-tagged one-time key, and typed PQ key. Signature verification authenticates the bytes passed to `validate_init_kex`; field position alone is never trusted. |
| AR-08 | Beacon/server DH1--DH4 and ML-KEM results are paired in the order represented by `PqxdhSharedSecrets`, and the exact core-built root transcript plus `PQXDH_INFO` is passed to deterministic HKDF. |
| AR-09 | The 64-byte initial-chain result is split into two exact 32-byte halves according to the core role offsets, using `SYM_RATCHET_INFO`; the concrete beacon-send/server-receive and server-send/beacon-receive states match. |
| AR-10 | Beacon construction maps the authentic compiled-in public key and numeric server identity-key ID to the exact `ServerBinding` stored by `BeaconFresh`; F* then proves field-by-field preservation through `BeaconInitSent`, candidate, authenticated response, and establishment. A separate acceptance theorem assumes no equality between the stored and accepting bindings: successful response-key preparation and authenticated sender-ID checking derive that both stored fields equal the accepting server candidate. The Phase-2 identity supplied to finish is exactly the parsed `identityKey`, while the authenticated sender ID and eight assigned-ID bytes supplied after the initial open are exactly its returned `CryptoFrame.keyId` and plaintext prefix. Initial trust-anchor authenticity plus wire/open provenance remain adapter assumptions; later peer-map contents do not redefine the expected binding. |
| AR-11 | `RegistrationStatus::Fresh` means the exact 64-byte semantic registration ID is absent from the persistent set. Successful server acceptance inserts it once and monotonically before any later response failure. One owner and no rollback/independent replica are required. |
| AR-12 | `KeyIdAvailability::Available` means the exact checked next ID is absent from the unique peer map. All recoverable failure points precede the final sequential peer/ratchet and counter assignments, which refine one logical commit but do not provide crash or concurrency atomicity; replay consumption intentionally occurs earlier. |
| AR-13 | A fresh beacon emits one registration bundle. Entropy/key material supplied as explicit core coins is fresh, and the production enum advances to `InitSent` or terminal abort without reusing a bundle. |
| AR-14 | The claimed production trace starts through successfully initialized or validated high-level `BeaconCryptPqxdh` APIs. Cap'n Proto, serde, allocation, FFI/bindings, persistence media, zeroization mechanics, replicas, and direct compatibility setters are not silently promoted to verified components. |
| AR-15 | Phase-2 `identityKey`, `ephemeralKey`, `kemCipherText`, `appCipherText`, and `keyId` encode respectively the candidate server identity, ephemeral X25519 public key, ML-KEM ciphertext, complete initial `CryptoFrame`, and proposed remote ID. The nested initial `CryptoFrame.keyId` is the candidate server identity-key ID. The beacon parses those same fields, compares `identityKey` with its retained public key, binds the public material into its DH/KEM/AD/decryption path, opens the frame against its retained numeric server ID, and accepts only when the authenticated frame sender and decrypted eight-byte assigned-ID prefix match the retained binding and outer `keyId` respectively. |
| AR-16 | A production `CryptoFrame` encodes `seq = key_seq`, `keyId = sender_kid`, and `cipherText = AEAD ciphertext || 16-byte tag || 64-byte CTX commitment`; the local `Encrypted.key_id = target_kid` is not placed on the wire. Receive treats the parsed sender ID only as a lookup hint, rechecks it in the selected helper, and rejects payload lengths no greater than the exact overhead before admitting the parsed sequence. It then passes the selected key/nonce, 153-byte associated data, parsed 16-byte tag, `seq`, and `keyId` to the F*-proved transcript helper, hashes the returned 229 bytes, and authenticates before consuming the key. ProVerif's symbolic forged frame starts after those parser/sender/length gates and does not prove their byte-level behavior. |
| AR-17 | The five named honest-task canaries are routed only to their intended honest-beacon sessions. The private `honest_origin`/`malicious_origin` tables and split server processes classify proof-model recipients; they are not production authorization checks and do not prove the surrounding C2's task-selection policy. Attacker-owned sessions receive only `MALICIOUS_TASK_SECRET`, whose deliberate disclosure is a non-vacuity control. |

## Proof-library and tool assumptions

| ID | Reviewed trusted surface |
| --- | --- |
| LA-01 | hax correctly translates the selected Rust semantics to the generated F* and ProVerif syntax. The deny-all item selectors and exact tool revision are fingerprinted/pinned, but compiler correctness is trusted. |
| LA-02 | PQXDH's and the commitment builder's exact slice proofs use the val-only contracts for `Rust_primitives.Hax.Monomorphized_update_at.{update_at_range,update_at_range_to,update_at_range_from}` from the pinned hax proof libraries. Their reviewed contracts replace precisely the selected range and preserve its prefix/suffix. |
| LA-03 | The PQXDH key-ID and commitment LE64 proofs call val-only `Rust_primitives.Integers.shift_right_lemma` for shifts 8 through 56. Its exact contract is `Lemma (v (shift_right a b) == v a / pow2 (v b))` with an SMT pattern for the shift; the underlying pinned `shift_right` is `opaque_to_smt`. The commitment decoder additionally calls the pinned val-only `pow2_values` contracts for exponents 8, 16, 24, 32, 40, 48, 56, and 64. |
| LA-04 | `update_at_usize`, `repeat`, `array_of_list`, slice copying, Option/Result, the other selected finite integer arithmetic/casts, equality, and `Core_models.Num.impl_u64__MAX` are transparent definitions in the locked hax/Core_models libraries. Ratchet extraction uses only the transparent single-index update. The commitment injectivity proof also uses the pinned checked `FStar.Math.Lemmas` division identities and `FStar.Seq.Base` sequence extensionality/equality lemmas. |
| LA-05 | F*, Z3, and their kernel/runtime correctly check the generated modules and handwritten lemmas under the locked flags. There is no local `assume`, `admit`, lax mode, or admitted-query flag. |
| LA-06 | ProVerif 2.05 soundly analyzes the stated symbolic model and the result classifier accurately enforces the complete expected result set. This is not a computational reduction for the production primitives. |

## Generated-code exceptions

Generated directories are regenerated and never hand-edited. Their exact file
sets and hashes are in the manifest, while the following exceptions explain
constructs that are accepted rather than silently treated as proved
production behavior.

| ID | Reviewed exception |
| --- | --- |
| GE-01 | The three F* files contain hax-generated module options and expose record constructors/fields that are private in Rust. Lemmas may construct records internally, so isolated field-preservation lemmas do not prove Rust typestate unforgeability; the composed PQXDH theorem calls the authentication transition explicitly. |
| GE-02 | Generated F* calls the val-only range-update contracts in LA-02; the handwritten key-ID and commitment proofs call the val-only shift lemma in LA-03, and the commitment decoder calls the listed val-only power-of-two contracts. `while_loop_return`, the opaque `u64::to_le_bytes` model, a derived whole-`ServerBinding` equality assumption, local `assume`, and local `admit` are not accepted exceptions and are rejected by policy/fingerprint drift. |
| GE-03 | `pro-verif/extraction/lib.pvl` contains hax's generated preamble and selected-type plumbing: the public channel `c`; `Option`, `Some`, `None`, and `Option_err`; the `empty` constant; bitstring, nat, and bool defaults; bitstring/nat errors; `nat_to_bitstring`; six selected nominal record types; twelve type converters; six arbitrary record default constants; and six record error helpers. There are nine error helpers total and eleven textual `construct_fail()` occurrences (declaration, reduction, and nine error paths). These are generated backend plumbing, not protocol constructors. |
| GE-04 | Handwritten ProVerif never calls a generated `from_bitstring`, default, or error helper. The only generated converter it calls is `RootKeyInput_to_bitstring`, exactly three times, to feed the ideal root constructor in the honest beacon, honest server, and malicious-registration server paths; every other converter is unused by the handwritten model. The gate enforces this allowlist. |
| GE-05 | Exactly three Rust `hax_lib::proverif::replace` fragments are permitted: `registration_id` projects identity plus one-time key; `build_root_key_input` preserves DH1, DH2, DH3, DH4, KEM order; and `build_associated_data` becomes a data constructor justified by the F* layout theorem. A fourth replacement fails the gate. |
| GE-06 | The ProVerif `build_root_key_input` replacement models its successful constructor path and omits Rust's all-zero-DH error. Modeled server/beacon processes invoke it after their ideal DH computations; F* separately proves exact zero-DH rejection. No ProVerif result is claimed for malformed core calls outside those processes. |
| GE-07 | The generated library's public constructors/accessors and arbitrary type converters are more permissive than Rust privacy. Modeled role processes construct private core values directly and never accept attacker-provided converter/default/error values. Agreement events carry values parsed from the public wire, not private shadow transcripts. |

The structural baseline for the generated ProVerif file is six selected types,
twelve converters, six record default constants, nineteen reductions total,
and the three required production-backed operations. The generated F* file set
is exactly the commitment, PQXDH, and ratchet modules.

## Handwritten backend fragments

The review atom is the entire listed file unless a smaller embedded fragment is
named. Consequently every declaration, equation, process, event, query, and
proof helper outside a generated directory belongs to exactly one entry below;
whole-file fingerprints force renewed review even when a structural count is
unchanged.

| ID | Handwritten review unit | Contents and status |
| --- | --- | --- |
| HB-01 | `proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst` | Logical cache view and strict counter, gap/capacity, one-step failed-authentication retention, zero-cost retry, consumption, replay, full-cache rejection, post-consumption capacity release, restore, send-key, and peer-isolation lemmas. Checked proof, not an axiom file. |
| HB-02 | `proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst` | Strict type/role layout, transcript, AD, ratchet split, expected-server binding preservation and mismatch rejection, authenticated sender/assigned-ID checks, acceptance-implies-binding-agreement, server transaction, and conditional honest-run lemmas. Checked proof, not an axiom file. |
| HB-03 | `proofs/pro-verif/crypto.pvl` | Four abstract sorts, 31 constructors/functions, six primitive reductions, and one `seal_frame` helper. This is the trusted symbolic primitive theory described by PL-02--PL-11. |
| HB-04 | `proofs/pro-verif/environment.pvl` | Wire and explicit failed-receive state/cache constructors; protocol, cache-lifecycle, failed-open, replay, and compromise events; two private origin tables; private ordinary and failed-receive snapshot channels; and the replay, role, malicious-registration, failed-receive, private-state, and compromise processes. Includes the bounded honest record prefix, an attacker-usable malicious registration response, and the exact 50-slot failed-open execution. |
| HB-05 | `proofs/pro-verif/queries.pvl` | Five baseline secrecy queries and six injective correspondences; all eleven must be true. |
| HB-06 | `proofs/pro-verif/reachability-queries.pvl` | Seven non-vacuity queries whose negations must be false: the original honest acceptance, replay rejection, abort, commit, and record-receive traces; malicious-registration response commit; and attacker derivation of the malicious-session canary. |
| HB-07 | `proofs/pro-verif/compromise-queries.pvl` | Two required positive deleted-key secrecy results and three required negative cached/live-chain secrecy results. |
| HB-08 | `proofs/pro-verif/baseline.pv` | Top-level replicated baseline process containing concurrent honest sessions and attacker-owned registrations. |
| HB-09 | `proofs/pro-verif/compromise.pv` | Top-level replicated synchronized late-compromise process for the honest-session snapshot; malicious registrations are exercised by the baseline isolation scenario instead. |
| HB-10 | Three `hax_lib::proverif::replace` attributes in `src/pqxdh.rs` | Embedded handwritten backend fragments described by GE-05 and GE-06. They are feature-gated and have no ordinary Rust runtime effect. |
| HB-11 | `proofs/pro-verif/check-results.awk` | Trusted result-control logic for the CTX/no-CTX differential control, baseline, original compromise, private failed-receive, and failed-receive-compromise result sets; scenario classification; rejection of timeout/inconclusive/missing/substituted results; and the required positive/negative secrecy, correspondence, and reachability splits. |
| HB-12 | `Makefile` and `proofs/fstar/Makefile` | Deny-all extraction selectors, backend composition, strict checker flags, expected-result invocation, generated drift checks, and this inventory gate. |
| HB-13 | `proofs/pro-verif/failed-receive.pv` | One exact, non-replicated server-to-beacon failed-active-receive execution synchronized with a private-state sink and composed with replicated attacker-owned beacon registration processes. The failed-receive record root is fresh and standalone rather than established by the registration process. |
| HB-14 | `proofs/pro-verif/failed-receive-queries.pvl` | Required private-state secrecy and state/origin correspondences for advancement before failed authentication, zero-cost retry, later honest acceptance, replay rejection, cache-capacity behavior, and admission after one slot is freed. |
| HB-15 | `proofs/pro-verif/failed-receive-reachability-queries.pvl` | Required negative reachability negations for every phase of the exact finite failed-receive execution, including cache fill, capacity rejection, honest delivery, replay rejection, and post-release admission, plus attacker-owned registration commit and malicious-canary recovery. |
| HB-16 | `proofs/pro-verif/failed-receive-compromise.pv` | One exact, non-replicated server-to-beacon failed-active-receive execution synchronized with disclosure of the legitimate receiver's post-failure snapshot before later delivery and composed with replicated attacker-owned beacon registration processes. The failed-receive record root is fresh and standalone. |
| HB-17 | `proofs/pro-verif/failed-receive-compromise-queries.pvl` | Required consumed-past secrecy and compromise-order results plus deliberate attacks on skipped, retained-target, and live-future secrecy and on honest-send provenance after target-key compromise. |
| HB-18 | `proofs/pro-verif/failed-receive-compromise-reachability-queries.pvl` | Required negative reachability negations witnessing both the synchronized post-failure compromise and a possible later honest delivery. |
| HB-19 | `proofs/fstar/Beaconcrypt_protocol_core.Commitment.Lemmas.fst` | Strict proof that the extracted 229-byte commitment transcript contains the key, nonce, associated data, AEAD tag, sequence, and sender ID at the exact fixed ranges; both LE64 encodings and the complete six-field input are injective; and `ctx_distinct_openings_imply_hash_collision` returns a valid collision witness for any two semantically distinct accepted explanations of one fixed payload under arbitrary pure hash and AEAD-open functions. Checked proof, not an axiom file. |
| HB-20 | `proofs/pro-verif/aead-commitment-negative-control.pvl` | Deliberately non-key-committing AEAD theory in which one ciphertext/tag opens to two fresh plaintexts under distinct constructed keys, nonces, and associated-data contexts, plus otherwise identical with-CTX and without-CTX processes. |
| HB-21 | `proofs/pro-verif/aead-commitment-negative-control-queries.pvl` | The single shared double-opening reachability query, required to have opposite classifications in the two top-level scenarios. |
| HB-22 | `proofs/pro-verif/aead-commitment.pv` | Top-level CTX negative-control process; collision-free `ctx_commitment` validation must make the double-opening event unreachable. |
| HB-23 | `proofs/pro-verif/aead-no-commitment.pv` | Top-level no-CTX negative-control process; removing only the commitment checks must make the same double-opening event reachable. |

The baseline ProVerif record model intentionally has one receive program point per sequence and uses a stronger ideal exact-opening AEAD rule. The separate HB-20--HB-23 differential control, not that ordinary rule, demonstrates the symbolic CTX benefit against a deliberate multi-opening. The dedicated failed-receive model instead repeats one invalid retained target, accepts a later frame at that target, rejects its replay, fills the exact 50-slot cache, rejects the next future target while full, and retries that future target after one slot is released. This is one finite execution, not an implicit arbitrary-schedule theorem; HB-01 supplies the general pure-state planning, one-step advancement, retention, consumption, and replay facts. The replay process is an explicit one-owner, non-rollback refinement for one bundle per fresh beacon identity, not a private validity oracle or a multi-replica theorem. Replicated attacker-owned beacons disclose all of their freshly generated secrets before registration, and the malicious server path accepts their valid self-signed bundles. That path conservatively treats every request as fresh: it strengthens the honest cross-recipient isolation test but proves neither replay behavior nor availability for malicious identities. The private origin tables implement the AR-17 proof classification and must not be interpreted as production ACLs. Attacker-owned registration does not activate `CompromiseFailedReceiveState`; that separate negative scenario explicitly discloses a legitimate receiver snapshot beyond the base threat model.

## Maintaining the inventory

`reviewed-inventory.txt` uses `category SHA-256 path`, with paths relative to
`crates/protocol-core`. It fingerprints the production Rust/schema surface,
core/extraction inputs, tool and CI controls, generated artifacts, every
handwritten backend file, the result classifier, and this document/checker.
The checker independently derives the production Rust/schema, core Rust,
generated, and handwritten backend file sets. It also compares every file of
any extension under `proofs/` with the manifest (the manifest itself is the
sole implicit self-referential entry) and rejects symlinks in monitored trees,
so a new helper cannot be hidden by its name, extension, or ignore status.

There is deliberately no automatic refresh target. For an intentional change:

1. review the changed production/proof boundary and update the applicable
   OR/PL/AR/LA/GE/HB entries;
2. regenerate both backends and run all proofs;
3. inspect every generated and handwritten diff;
4. update only the affected manifest digests; and
5. run `make check-inventory` and `make check-generated`.

Hash churn is intentionally conservative. A comment-only edit to a monitored
file still requires an explicit baseline update, because the gate cannot
reliably distinguish semantic from non-semantic proof-boundary changes.
