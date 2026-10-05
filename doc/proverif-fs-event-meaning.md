# Free-schedule ProVerif event meanings (L6)

This document fixes what every event of the free-schedule (fs) ProVerif family means as an outcome of the Rust API, and therefore what each fs claim says about Rust. It is obligation L6 (event projection) of the staged ProVerif plan for audit findings F2, F13 and F11. Stage P0 wrote it as a paper draft outside the repository and stage P1 applied it; this is the maintained version, with every Rust citation re-checked at commit `9e588c6`. As maintained reference documentation it lives directly in `doc/`; it was first committed, and reviewed, as `doc/impl/proverif-fs-event-meaning.md`. The [fs-registration guide](impl/proverif-free-schedule-registration.md) records the P1 model, its results and its deviations, and the [analysis document](formal-verification-analysis.md#free-schedule-proverif-registration-fs-registration) explains the results in plain English. Each event is declared with a short comment in `beaconcrypt-core/proofs/pro-verif/fs-common.pvl`; where that comment and this document differ in detail, this document is the reference ([Changes from the P0 draft](#changes-from-the-p0-draft)).

Status: the plan requires a separate review of L6 before any record claim relies on it. That review was made at the start of stage P2 on commit `f381479`; it approved the document with four minor findings and two sets of nits, all of which this version applies ([Review record](#review-record)). L6 is therefore a reviewed paper argument. The P2 review that followed changed two event declarations, which this version describes but which have not been reviewed separately: `FsReceiveRejected` now carries the refused frame, and the witness-only event `FsReceivedFrame` carries every accepted frame ([Changes after the L6 review](#changes-after-the-l6-review)). L1 and L5 (registration scheduling and Beacon lifecycle) and L2, L3 and L4 (records) remain pending paper arguments, and every Rust reading below is conditional on them and is cited as pending. Nothing in this document is a ProVerif result, and no ProVerif run was made for it.

Every fs result is a symbolic result (Dolev-Yao attacker, free constructors, ideal hash, KDF and AEAD) for a bounded process, never a computational bound. This projection says how such a result reads as a statement about Rust calls. It adds nothing to the model (no axiom, restriction, lemma or proof-only process), and it does not discharge [global closure item 1](impl/handover/pause-2026-10-01/README.md#remaining-global-closure-work) (arbitrary reached committed states), which owner decision OD1 leaves to the Lean side.

## Basis

The Rust basis is commit `9e588c6` of branch `codex/full-proof-composition`. Its Rust sources are identical to `959cdab`, the basis of the plan and of the P0 spike, and to `533901f`, the basis named in the P1 guide: `git diff 959cdab 9e588c6 -- beaconcrypt/src beaconcrypt-core/src` is empty. The Rust code is authoritative; where the model and Rust differ, the model follows Rust. The branch `vcvio` (`8330cde`) is an ancestor that lacks the Beacon sequence-one gate (`beacon.rs:468-470` here, added by `5cbd76e`); on that branch the C-NOGATE mutant of the record scenarios is real behaviour (the HB-95 later-record substitution, see [Server-to-Beacon records](#server-to-beacon-records-fs-records-s2b-stage-p2)).

Every file:line below was checked by reading the file at `9e588c6`. No test pins the citations of this document: the transcript-fidelity test pins only the annotations in the model files, and only by the first line of each range. A change to a cited Rust file requires re-checking this document by hand and updating the commit named here.

Paths: `server.rs`, `beacon.rs`, `ratchet.rs`, `shared.rs`, `ser.rs`, `deser.rs`, `lib.rs`, `cbinds.rs`, `pybinds.rs` and `persistence.rs` are under `beaconcrypt/src/`; "adapter `pqxdh.rs`" is `beaconcrypt/src/pqxdh.rs`; `pqxdh.rs` alone is `beaconcrypt-core/src/pqxdh.rs`; `pqxdh/concrete.rs` is `beaconcrypt-core/src/pqxdh/concrete.rs`; `record.rs` is `beaconcrypt-core/src/record.rs`; `concrete.rs`, `control.rs` and `refined.rs` are under `beaconcrypt-core/src/ratchet/`; `crypto.pvl`, `fs-common.pvl` and `fs-registration.pvl` are under `beaconcrypt-core/proofs/pro-verif/`.

## Conventions

### Rust runs and events

A Rust run is a finite sequence of public calls on `Server` and `Beacon` objects, chosen by the environment: the local application together with the network adversary. Every call takes `&mut self`, so the calls on one object are totally ordered and each is atomic for that object; calls on different objects commute. Neither type derives `Clone` (`server.rs:26-32`; `beacon.rs:44-49`), so an object is duplicated only by persistence, which is out of scope.

Each fs event is a predicate on one Rust call: which function was called on which object, which value it returned (`Some` or `None`, and the returned bytes) and which state change it committed. Event order is call order. Inside one call the model emits the event and then outputs the returned public value, whereas Rust commits the state change and then returns; nothing can interleave on that object between the two, so the orders agree.

### Field kinds

Each event field has one of the following kinds, given per event below.

| Kind | Meaning |
| --- | --- |
| arg | A call argument, or a value the call decodes from its argument |
| ret | A value the call returns to the application |
| token | A field of the opaque `RegistrationOutput` token (`pub(crate)` fields, `server.rs:39-42`), which the application holds but cannot read |
| state | A component of the object's state before or after the call; some are also readable through public accessors |
| derived | A deterministic function of argument or state values that Rust never computes at that call |
| local | A value computed inside the call and dropped before it returns |
| ghost | None of the above: a value defined only from the run history, such as the root from which a ratchet was initialised |
| label | The identity of the object called (`obj`), not a byte value |

A claim that mentions a token, derived, local or ghost field quantifies over it as a function of the run; no Rust caller observes it at that event. `fs-common.pvl` and the P1 guide group four fields as "ghost fields", and the analysis document lists the same four as fields that the call does not return: `root` on build and record events, `init` at the build, `rid` at the Beacon and `kid` on Beacon receives. The finer classification here is: `root` at the build is a token field and a ghost on record events; `init` at the build is a ghost; `rid` at the Beacon is derived; `kid` on Beacon receives is state (the Beacon's stored assigned ID, readable through `identity_key_kid`, `beacon.rs:84-86`). The difference changes no query and no claim.

### Scope

Out of scope: Cap'n Proto (messages are abstract byte strings that each side can decode), persistence and restoration (`PersistentServer`, `persistence.rs`, `serialize_state` and `deserialize_state` at `server.rs:278-299`), attacker access to the running process, and libsodium internals (a black-box functional contract). Owner decision OD2: the Server's protocol identity is its identity key, and the proof Server is an idealisation with perfect key management (uniform independent private keys, never disclosed; secret state such as ratchets never disclosed) and no backup or restore. Two objects built from the same seed are the same Server for the protocol, and replay claims are per live object.

The C and Python bindings, and the Go binding through the C API, hold a `BindingServer` persistence wrapper (`cbinds.rs:11`; `pybinds.rs:84-87`) whose methods run the same `Server` calls inside a commit (`persistence.rs:412-425`). The wrapper is persistence and out of scope; the projection applies to the inner `Server` calls. Both bindings call accept and build back to back on one object (`cbinds.rs:280-286`; `pybinds.rs:125-128`), which is exactly the model's adjacency.

The legacy HB-89 [registration event projection](impl/registration-event-projection.md) concerns the legacy fixed-schedule scenarios and is unrelated to the fs events.

## The capability/value mismatch

Global closure item 1 names "the capability/value mismatch". It has two halves. The capability half is the set of operations the environment can invoke: the Rust public API (`lib.rs:60-81`) offers more operations than the fs processes have steps, and the fs processes give some choices that Rust leaves to the local application (when to build, when to send, with which plaintext) to the network attacker. The value half is that Rust calls return optional byte values to a local caller, whereas fs events carry symbolic terms, several of which no Rust call returns, and ProVerif's attacker knowledge is the deduction closure of what the processes output. The symbolic-interface audit (`doc/impl/handover/pause-2026-10-01/integrated-evidence/symbolic-interface-audit.tar.gz`) states the same gap for the legacy model. The two subsections below fix both halves for the fs family; the events section then fixes each event.

### Capabilities

| Rust public call | Location | fs representation | Relation |
| --- | --- | --- | --- |
| `Server::try_new`, `Server::new(server_kid, id_seed)` | `server.rs:148-168` | `new obj` under a replication; every object uses `SERVER_IDENTITY_SECRET` and the own ID `SERVER_KEY_ID`. The Rust counter starts at `server_kid` (`server.rs:164`), so the first peer ID is `fs_kid(1)` (`pqxdh.rs:838-844`) | One identity and one `server_kid` (OD2) |
| `get_shared_secret(buffer)` | `server.rs:332-422` | One Server-object step on a `[precise]` attacker input | Exact up to codec and primitive idealisations |
| `build_registration_response(reg_out, data)` | `server.rs:424-502` | Attacker-chosen build or drop directly after the accept, on the same object; `data` is a fresh name | Rescheduled (pending L1 (i)-(v)); payload restricted (E7) |
| `Server::encrypt_message`, `encrypt_and_update`, `encrypt_and_update_json` | `server.rs:224-228`, `:504-518` | Server peer send step on an attacker input | Timing over-approximated; plaintext form per scenario (E7) |
| `Server::decrypt_message`, `decrypt_and_update`, `decrypt_and_update_json` | `server.rs:229-250`, `:520-532` | Server peer receive step (b2s) on an attacker input | Routing over-approximated by merged IDs (E5, pending L2) |
| `Beacon::try_new`, `Beacon::new(server_kid, server_id_pk)` | `beacon.rs:59-83` | `FsBeacon()` under a replication, with fresh identity, prekey, one-time and ML-KEM secrets and the pin `(S, SERVER_KEY_ID)` | Pin restricted (E3) |
| `get_registration_bundle()` | `beacon.rs:300-399` | The Beacon's single signed-bundle output | Exact up to L5 (pending) |
| `finish_registration(bytes)` | `beacon.rs:402-510` | One finish on an attacker input; any failure stops the process | Exact up to bounds and L5 (pending) |
| `Beacon::encrypt_message`, `Beacon::decrypt_message` | `beacon.rs:152-174` | Beacon send steps (b2s); Beacon receive window (s2b) | As for the Server |
| `new_onetime_keypair`, `delete_onetime_keypair`, `delete_pq_keypair` | `beacon.rs:222-296` | None | A one-time key drawn before the bundle is indistinguishable from the fresh one-time secret drawn at bundle time; the deletions abort the object or return it to `Fresh`, which only removes traces |
| Secret accessors `identity_sk` (`server.rs:179-181`; `beacon.rs:90-92`), `pq_sk` (`beacon.rs:114-121`), `get_prekey_sk` (`beacon.rs:193-200`), `get_onetime_sk` (`beacon.rs:210-216`) | as listed | None | Excluded: no reveals in the no-reveal claims (OD2) |
| `RatchetSnapshot` inside `SendState` and `RecvState` | `server.rs:70-110`; `ser.rs:195-213` (both chains, both counters and every cached key) | Never output | Excluded: secret ratchet state is never disclosed (OD2) |
| Public accessors `identity_pk`, `identity_key_kid`, `server_kid`, `pk_by_kid`, `ratchet_status` (`server.rs:173-178`, `:182-184`, `:204-209`); `identity_pk`, `identity_key_kid`, `server_id`, `server_kid`, `pq_pk`, `associated_data`, `ratchet_status`, `get_prekey_pk`, `get_onetime_pk` (`beacon.rs:84-89`, `:93-113`, `:129-142`, `:184-191`, `:202-208`) | as listed | None needed | Keys are in a bundle or response or are deployment constants, the AD is a public function of the two identities (`pqxdh.rs:922-947`), and counters are non-secret metadata |
| Test-only helpers `set_identity_kid`, `add_known_kid`, `delete_known_kid`, `new_remote_kid`, `set_associated_data` | `server.rs:169-172`, `:185-203`; `beacon.rs:143-151` | None | `#[cfg(test)]`, not public API |

Calls made in the wrong state return `None` with no state change and no output: a bundle request outside `Fresh` and `FreshWithCoins` (`beacon.rs:333`), a finish outside `InitSent` (`beacon.rs:403-406`), a Beacon encrypt or decrypt outside `Established` (`beacon.rs:154-161`, `:165-172`), and a Server encrypt to an uninstalled ID (`server.rs:225`, `:227`). The model has no step for them, which is exact: deleting such a call from a Rust run changes no state, no output and no event.

### Values

- **V1, published returns.** The bytes returned by `get_registration_bundle` (`beacon.rs:398`), by `build_registration_response` (`RegResponse.serialized` and `.kid`, `server.rs:498-501`) and by the encrypt calls (`Encrypted.ciphertext`, `ratchet.rs:401-405`) are network messages: the model outputs them on the public channel. This over-approximates the Rust adversary, which sees them only if the application forwards them. `RegResponse.kid` also travels inside the response (`server.rs:482`). `Encrypted.seq`, `Decrypted.seq` and `Decrypted.key_id` repeat frame fields (sequence and sender); `Encrypted.key_id` is the caller's target (`ratchet.rs:403`).
- **V2, local returns, never published.** The `RegistrationOutput` token (`pub(crate)` fields, no `Clone`, `server.rs:39-42`), returned plaintexts (`Decrypted.plaintext`, `ratchet.rs:485-489`; the finish's `Some(plaintext)`, `beacon.rs:509`), `RatchetSnapshot` and the secret accessors. The model never outputs them: a returned plaintext is an observation of the local application, not network output. The Rust reading of every secrecy claim therefore assumes that the application does not disclose these values.
- **V3, `Some` or `None`.** Every Rust failure of a call returns the same `None`, so the caller cannot tell which check failed. Events that name a failure cause (`FsServerReplayRejected`, `FsServerAcceptFailed`, `FsBeaconFinishOpenedLater`, `FsReceiveRejected`) are finer than the API outcome: they are defined by the internal branch reached, and they appear only in witnesses, definitional checks and controls, never in a security result. The model does not publish the `Some`/`None` bit of calls whose success produces no output (receives, finish). For correspondences and weak secrecy this changes nothing, because ProVerif already explores every attacker choice and a bit adds no term to deduce from; for the diff-equivalences of stage P5 the attacker must receive it (E11).
- **V4, terms and bytes.** Event fields are byte strings in Rust and terms in the model. A term denotes the bytes that the libsodium black box and the core compute for it. A field equality in a query is a byte equality in Rust only under the idealisations of the theory: free Ed25519 signatures, HKDF as one random-oracle stream, committing AEAD with CTX, injective `[data]` encodings, and the `crypto.pvl` X25519 and ML-KEM theory. `init` is the verified key tuple (`pqxdh.rs:325-345`), never the signed blobs, so A1 and A2 do not need unique signature encodings.
- **V5, fields that Rust does not return.** Token, derived, local and ghost fields ([Field kinds](#field-kinds)). A Rust reading of a claim quantifies over them as functions of the run history.
- **V6, application choices.** Where Rust lets the application choose a value, the model either hands the choice to the attacker (timing, build or drop: an over-approximation) or fixes it to a fresh name (registration payload, record plaintexts: a restriction, E7). The Rust reading of a claim that mentions such a value is about values of the modelled form.

## Common fields

| Field | Rust meaning | Kind |
| --- | --- | --- |
| `S` | Server side: the object's `identity_pk` (`server.rs:176-178`), which also enters the AD (`server.rs:218-223`; `pqxdh.rs:877-880`) and the response (`server.rs:484`). Beacon side: the pinned key `server_id_pk` given to `Beacon::try_new` (`beacon.rs:67-68`, `:73-76`, `:81`), held as `expected_server_binding.identity_public_key` (`pqxdh.rs:96-99`, `:257-275`); the bundle does not contain it (`pqxdh.rs:314-319`). In the model always `ed_public(SERVER_IDENTITY_SECRET)` | state |
| `B` | Beacon side: the object's `identity_pk`, generated in the constructor and never imported (`beacon.rs:70`, `:87-89`). Server accept: `remote_id`, decoded from the tagged identity and used to verify the three signatures (`server.rs:337-346`). Server build and records: the identity installed under `kid` (`server.rs:452-453`, `:493-495`), readable as `pk_by_kid(kid)` (`server.rs:204-206`). `known_ids` entries are never replaced or removed outside test helpers and persistence | state or arg |
| `k` | Query variable only: the Ed25519 secret behind `B`. `attacker(k)` means the adversary holds that secret, that is, `B` is an identity it built. For a Beacon object, `k` is the secret generated at `beacon.rs:70`, never disclosed in scope | ghost |
| `obj` | The Server object receiving the call (`&mut self`) | label |
| `init` | `VerifiedInitKex`, the untagged `(identity, prekey, one_time, pq)` public keys. Server accept: `verified_registration` (`server.rs:347-353`; `pqxdh.rs:325-345`). Beacon: the untagging of the `InitKex` it signed, which is the object's own four public keys (`beacon.rs:335-345`; `pqxdh.rs:304-321`; the untag functions at `pqxdh.rs:977-1006` invert the tags at `:949-975`). At `FsServerCommitted`: the `init` of the accept that produced the token; `PendingServerRegistration` keeps the registration ID and `B` but not the prekey or the ML-KEM key (`pqxdh.rs:720-727`) | arg, derived or ghost |
| `rid` | `RegistrationId` = `identity_pk ‖ one_time_pk`, 64 bytes, compared by exact equality (`pqxdh.rs:195-204`; hax replacement `:212-220`). Server: computed at `server.rs:354`. Beacon: never computed; a function of its identity and one-time key | arg or derived |
| `kid` | The peer's assigned key ID: `server_kid + n` for the n-th successful build on the object (`server.rs:164`, `:434`; `pqxdh.rs:838-844`). Server build: `remote_kid` (`server.rs:450`), returned as `RegResponse.kid`. Beacon finish: the response's `key_id` (`beacon.rs:452`), authenticated by the binding (`pqxdh.rs:616-628`) and stored at `beacon.rs:503`. Server send: the target argument. Server receive: the claimed sender, returned as `Decrypted.key_id` (`server.rs:237`; `record.rs:176`). Beacon send: the frame's sender field `identity_key_kid` (`beacon.rs:153`); `Encrypted.key_id` is the Server's ID there (`beacon.rs:162`). Beacon receive: the stored `identity_key_kid`; `Decrypted.key_id` is the Server's ID there (`beacon.rs:173`). Model: `fs_kid(n)` in fs-registration, the constant `fs_kid(1)` in the record scenarios | arg, ret or state |
| `root` | The 32-byte `KexDerivedSecret` (`shared.rs:41`, `:427`) = HKDF-SHA-512 with no salt over the 192-byte root input and `PQXDH_INFO` (adapter `pqxdh.rs:46-59`), computed at `server.rs:414` and `beacon.rs:458`. It derives the initial chains once (`server.rs:456-457`; `beacon.rs:459-460`; `pqxdh/concrete.rs:64-115`; offsets `pqxdh.rs:428-435`) and is then dropped; it is never stored in an object and never returned to the application in readable form (the Server returns it only inside the opaque token, `server.rs:418-421`). Model: `pqxdh_root(...)` (`crypto.pvl:67-68`) | token, local or ghost |
| `ad` | The 153-byte AD `build_associated_data(S, B)` (`pqxdh.rs:922-947`). Server: `candidate.associated_data()` (`server.rs:458`; `pqxdh.rs:877-880`), computed at the build and never stored (an installed peer holds only its key and ratchet, `shared.rs:431-434`), and recomputed from the stored identities for each record call (`server.rs:218-223`). Beacon: the candidate AD (`beacon.rs:461`; `pqxdh.rs:552-555`), stored in `Established` (`beacon.rs:506`) and readable through `associated_data` (`beacon.rs:129-136`) | Server: local at the build, derived on record calls; Beacon: state |
| `payload` | The registration application plaintext. Server: `data.unwrap_or(REGISTRATION_WITNESS)` (`server.rs:459`; the single byte 0xFF, `shared.rs:50`), nonempty (`server.rs:460-462`). Beacon: the returned plaintext after the 8-byte binding is stripped (`beacon.rs:476-477`, `:509`) | arg or ret |
| `dir` | `server_to_beacon()` or `beacon_to_server()`: which initial chain. The Server sends on offset 0 and receives on offset 32; the Beacon reverses them (`pqxdh.rs:428-435`; `crypto.pvl:72-80`) | constant |
| `t` | The u64 frame sequence (`Encrypted.seq`, `ratchet.rs:404`; `Decrypted.seq`, `record.rs:177`); model `fs_seq(t)` in frames and the `nat` `t` in events | ret |
| `m` | The authenticated record plaintext: the send argument `bytes` (`ratchet.rs:414-420`) or `Decrypted.plaintext`. For t = 1 it is `binding ‖ payload` (`server.rs:463-470`; `beacon.rs:472`) | arg or ret |

## Events

`fs-common.pvl` declares twelve events (eleven when L6 was reviewed; `FsReceivedFrame` was added after the P2 review). The registration events are emitted by `fs-registration.pvl` (stage P1), the Server-to-Beacon record events by `fs-records-s2b` (stage P2, [records guide](impl/proverif-free-schedule-records.md)), and the Beacon-to-Server record events will be emitted by `fs-records-b2s` (stage P3), whose emission points below follow the P0 spike model. The P2 model files cite the Rust lines given here, and the transcript-fidelity test pins those citations.

### FsBeaconStarted(S, B, init, rid)

Model: `fs-registration.pvl:252`, immediately before the signed bundle is output; the record scenarios use the same Beacon prefix.

Rust outcome: `get_registration_bundle()` returned `Some(buffer)` (`beacon.rs:398`). Success condition: the state was `Fresh` or `FreshWithCoins` (`beacon.rs:306-334`), the one-time key generation in `Fresh` (`beacon.rs:301-305`), the three signatures and the serialisation (`beacon.rs:346-357`) succeeded. State change: `Fresh` or `FreshWithCoins` becomes `InitSent{control: started.state, prekey, onetime_key, pq_key}` (`beacon.rs:359-397`; `pqxdh.rs:304-321`). Returned: the bundle with the tagged identity and the three signed tagged keys (V1).

Fields: `S` is the pin (state); `B` is the object's identity (state, `beacon.rs:338`); `init` is derived from state, the object's own four public keys; `rid` is derived (`B ‖ one_time_pk`). After the call, `init` and `rid` are computable from the public accessors `identity_pk`, `get_prekey_pk`, `get_onetime_pk` and `pq_pk`.

Failure: `None` with no state change if any step before `beacon.rs:359` fails; the two `None` branches after it (`beacon.rs:365-372`, `:393-396`) restore the entry state and are unreachable after the state match at `:306-334`. A retry in `Fresh` draws a new one-time key (`beacon.rs:301-302`), so an object may draw several one-time keys and sign several times, but it returns at most one bundle: after a success the state is `InitSent` and every further call returns `None` (`beacon.rs:333`). The keys and signatures of failed attempts are never output, so the model's single one-time secret is exact. This is part of the pending lifecycle argument L5.

Coarser or finer: (a) `S` is not in the bundle; it is the Beacon's pin, and every model Beacon pins the honest Server key (E3). (b) `rid` is derived. (c) `new_onetime_keypair` before the bundle (`beacon.rs:222-255`) is equivalent to drawing the one-time secret at bundle time; the deletions (`beacon.rs:257-296`) end the object or return it to `Fresh` and emit nothing.

### FsServerAccepted(obj, S, B, init, rid, root)

Model: `fs-registration.pvl:133-140`, after the consumed-set insertion (`:126-131`) and before the build-or-drop input. The record scenarios follow the same order with one bundle per object, and therefore without the consumed-set branch, except that they draw the ephemeral secret and the KEM coins when the object starts ((c) below).

Rust outcome: `get_shared_secret(buffer)` on `obj` returned `Some(RegistrationOutput)` (`server.rs:418-421`). Success condition, in Rust order: decode (`server.rs:334-336`), identity size and tag (`:337-341`), Ed25519 key decode (`:342`), signatures over the ML-KEM, prekey and one-time keys (`:343-346`), `validate_init_kex` (`:347-353`), registration ID (`:354`), ID not consumed (`:355-360`), capacity reservation (`:361`), X25519 key decodes (`:362-367`), fresh ephemeral (`:368`), ML-KEM key decode and encapsulation (`:369-373`), Ed25519-to-X25519 conversions (`:374-375`), DH1-DH4 with libsodium's refusal of an all-zero output (`:376-394`), the shared-secret size conversion (`:395`), `server_accept` with the core all-zero check (`:396-411`; `pqxdh.rs:748-775`, `:383-389`), root derivation (`server.rs:414`). State change: `consumed_registrations := consumed_registrations ∪ {rid}` (`server.rs:415`) and nothing else. This call never writes `self.control` (the core returns it unchanged, debug assertion at `server.rs:412`), and no peer is installed. Outside construction (`server.rs:166`) and persistence (`server.rs:278-299`) the set is used only at `server.rs:355`, `:361` and `:415`, so it never loses an element. Returned: the opaque token (V2).

Fields: `S` = `identity_pk` (state, `server.rs:401`); `B` = `remote_id` (arg, `server.rs:342`); `init` = `verified_registration` (arg, `server.rs:353`); `rid` (arg, `server.rs:354`); `root` = `derived_secret` (token, `server.rs:414`, returned inside the token at `:418-421`).

Coarser or finer: (a) In the model the build-or-drop decision follows at once, on the same object. In Rust the application may hold several tokens, build them later and in another order, never build them, or build one on another live object with the same identity key and `server_kid` (`server_prepare_commit` checks only that binding, `pqxdh.rs:853-858`). These are cases (i)-(iv) of the pending L1, and case (iv) is open: OD2 does not exclude it. (b) The token is never output, so the attacker never obtains `root` from it, as in Rust. (c) In the record scenarios the Server ephemeral secret and KEM coins are drawn when the object starts (the "v2" form) rather than at `server.rs:368` and `:373`. With one bundle per object, neither value is used before the point where Rust draws it or output before the response, and a failed accept discards them in both orders, so the reorder changes no event; the trace-equivalence justification is written in [records guide step 2](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications) and has not yet been reviewed separately (E20).

### FsServerReplayRejected(obj, S, B, rid)

Model: `fs-registration.pvl:89`, when the computed `rid` is in the object's consumed slots; the state is unchanged. Not emitted in the record scenarios, where each object processes one bundle.

Rust outcome: `get_shared_secret` returned `None` at `server.rs:360` because the status was `Consumed` (`server.rs:355-359`; `validate_registration_status` returns `RegistrationReplay`, `pqxdh.rs:245-251`), after every check up to `server.rs:354` passed. No state change.

Fields: `S` (state); `B` and `rid` from the verified bundle (arg).

Finer than the API: the caller sees only `None` (V3). Used by R2 (definitional) and R3 (witness) only.

### FsServerAcceptFailed(obj, S, B, rid)

Model: `fs-registration.pvl:210`, when the tuple of the four DH calls (`:103-108`) fails after the consumed check. Under `crypto.pvl` a DH destructor fails exactly on an input that is not `x25519_public(_)` (`crypto.pvl:32-37`), so the event arises only when the prekey is not an X25519 public key (DH1 and DH3) or the one-time key is not (DH4). In the theory the identity conversion (`crypto.pvl:28-30`) and DH2 cannot fail, because an identity that verified the signatures is an Ed25519 public key there. This is a property of `crypto.pvl`, not of Rust: in Rust the conversion of the Beacon identity can fail after the signatures verified (see below).

Rust outcome: `get_shared_secret` returned `None` at one of `server.rs:361-414` after the status check found `Fresh`. The consumed set is unchanged (only its spare capacity may have grown at `:361`), the counter and the peers are unchanged, and the fresh ephemeral and KEM coins are discarded.

Coarser than Rust: the event stands for Rust's DH refusals, namely libsodium's refusal of an all-zero result (`server.rs:376-394`) and the core all-zero check (`pqxdh.rs:383-389`, reached through `server.rs:396-411`; the hax replacement at `pqxdh.rs:374-379` omits it). Rust accepts any 32-byte string as an X25519 public key (`server.rs:362-367`), so a model input that is not a point stands in for a low-order point; under `crypto.pvl` the core check can never reject a value that reached it ([guide step 3](impl/proverif-free-schedule-registration.md#model-steps-and-their-justifications)). The event does not cover the reservation (`server.rs:361`), the key decodes (`:362-367`, `:369-372`), randomness (`:368`), encapsulation (`:373`), the conversion of the Beacon identity (`:374`, which libsodium refuses for a key outside the prime-order subgroup even when that key verified the signatures: Ed25519 verification checks only that the key is canonical and not of small order, whereas the conversion also requires the main subgroup), the own-key conversion (`:375`), the size conversions (`:395`, `:405`) or HKDF failure (`:414`). Each of those returns `None` with no state change and no output, so deleting the call from a Rust run leaves the state, the outputs and every other event unchanged (case (v) of the pending L1); only this witness event is lost. Used by R5 only. R5 therefore does not witness the all-zero check itself; a distinguishing event is a stage P4 item.

### FsServerCommitted(obj, S, B, init, kid, root, ad, payload)

Model: `fs-registration.pvl:175-184`, after the attacker chose "build" and the sequence-one frame was sealed, immediately before the response is output. In the record scenarios it is emitted together with `FsSent(server_to_beacon(), S, B, kid, root, 1, binding ‖ payload)`.

Rust outcome: `build_registration_response(reg_out, data)` on `obj` returned `Some(RegResponse{serialized, kid})` (`server.rs:498-501`). Success condition, in Rust order: next ID (`server.rs:434`; `pqxdh.rs:838-844`), occupancy `Available` (`server.rs:435-439`), `server_prepare_commit` with the binding check (`server.rs:440-449`; `pqxdh.rs:847-882`, check at `:853-858`), Beacon key decode (`server.rs:452-453`), reservation (`:455`), fresh ratchet from `root` (`:456-457`), nonempty payload (`:459-462`), `binding ‖ payload` (`:463-470`), seal at sequence 1 with the Server's own ID as sender (`:471-479`), response serialisation (`:480-488`). State change: `known_ids[kid] := (B, ratchet)` with send sequence 1 and receive sequence 0 (`server.rs:489-496`), then `self.control := next_control`, so that `last_key_id = kid` (`server.rs:497`; `pqxdh.rs:905-914`).

Fields: `obj` is the building object (label); `S` = `identity_pk` (state, `server.rs:444`); `B` = `candidate.beacon_identity_public_key` (from the token, `pqxdh.rs:872`; installed state after the call); `init` is a ghost, the `init` of the accept that produced `reg_out`; `kid` = `remote_kid` (`server.rs:450`; ret, and state after the call); `root` is a token field (`reg_out.derived_secret`, `server.rs:430-433`, `:456`), dropped once the chains are derived; `ad` (local, `server.rs:458`: computed from the two identities and not stored); `payload` (arg, `server.rs:459`).

Failure: `None` at any step above. `reg_out` was moved into the call (`server.rs:430-433`) and is gone, the counter and the peers are unchanged, and the registration ID stays consumed (trait documentation, `server.rs:113-117`). This is exactly the model's drop branch (`fs-registration.pvl:199-203`), which emits nothing.

Coarser or finer: (a) Under case (iv) of the pending L1 the building object can differ from the accepting object; the model never builds on another object. (b) `init` is a ghost and `root` a token field. (c) `Occupied` and ID exhaustion are not modelled; both return `None` without a state change, which is the model's drop branch. `Occupied` is reachable only through the test helpers (`server.rs:185-203`): a restored state cannot produce it, because deserialisation rejects any known ID above the counter (`deser.rs:384-389`) and the next ID is the counter plus one. Exhaustion happens when the counter is already `u64::MAX` (`pqxdh.rs:838-844`), so a Server object reaches it within its first K_reg builds exactly when `server_kid + K_reg > u64::MAX`, for example at its first build when `server_kid = u64::MAX` (`server.rs:154-164`). The bridge `fs_kid(n)` stands for `server_kid + n` without wrapping (`fs-common.pvl:24-31`), so the model's successful builds correspond to Rust builds only when `server_kid + K_reg <= u64::MAX`. In other runs the model has extra successful builds, while each exhausted Rust build is a drop, so the model over-approximates them and no security claim is affected. (d) The payload is a fresh name, whereas Rust lets the application pass any nonempty `data` or `None`, which selects the public byte 0xFF (E7).

### FsBeaconEstablished(S, B, init, kid, root, ad, payload)

Model: `fs-registration.pvl:332-340`, after the sequence-one open, the binding check and the pin check. In the record scenarios it is followed by `FsReceived` at t = 1 and then by the Beacon's record workers.

Rust outcome: `finish_registration(bytes)` returned `Some(plaintext)` (`beacon.rs:509`). Success condition, in Rust order: state `InitSent` (`beacon.rs:403-406`), response decode (`:422-431`), identity conversions (`:432-433`), ML-KEM decapsulation (`:434`), DH1-DH4 (`:435-449`), `beacon_prepare_finish` with the pinned-identity check and the all-zero check (`:450-457`; `pqxdh.rs:541-562`), root (`beacon.rs:458`), fresh ratchet (`:459-460`), general receive on that ratchet with the pinned Server ID as expected sender (`:462-467`), `decrypted.seq == 1` (`:468-470`), plaintext longer than the 8-byte binding (`:473-475`), split and binding check (`:476-484`; `pqxdh.rs:616-628`), pin checks (`beacon.rs:493-502`). State change: `InitSent` becomes `Established{control: beacon_commit(...), associated_data, ratchet}` with receive sequence 1, an empty cache and send sequence 0, and `identity_key_kid := kid` (`beacon.rs:503-508`; `pqxdh.rs:667-673`).

Fields: `S` is the pin (state; `pqxdh.rs:545-547`, `:557`); `B` the object's identity (state); `init` its own key tuple in the entry state (`Established` no longer holds the prekey, one-time or ML-KEM key, `beacon.rs:33-37`); `kid` the authenticated response ID (arg, `beacon.rs:452`; state after the call); `root` = `derived_secret` (local, `beacon.rs:458`); `ad` (state after the call, `beacon.rs:461`, `:506`); `payload` the returned plaintext (ret, V2).

Failure: any failure in `beacon.rs:408-502` sets `Aborted` and returns `None` (`beacon.rs:176-182`, `:488-491`, `:495-501`); every later finish, encrypt or decrypt returns `None`. The model stops the Beacon process, which is exact given the pending L5 (at most one finish, no retry).

Coarser or finer: (a) The adapter pin checks at `beacon.rs:493-502` cannot fail after the core check, because the candidate's binding is the expected binding (`pqxdh.rs:545-547`, `:557`); the model's single equality test (`fs-registration.pvl:285`) stands for both. (b) fs-registration omits the nonempty check (`beacon.rs:473-475`), which can only reject; model payloads are never empty. (c) fs-registration opens the response frame only at `fs_seq(1)` (`fs-registration.pvl:315`), which is exact for every event of that scenario ([guide step 4](impl/proverif-free-schedule-registration.md#model-steps-and-their-justifications)); the record scenarios also open t in 2..T_max before the gate, to produce `FsBeaconFinishOpenedLater`.

### FsBeaconFinishOpenedLater(S, B, t)

Model (`fs-records-s2b.pvl`): the finish opened the response frame with the material for t in 2..T_max and emitted this event; the gate library then ends the Beacon (`fs-records-s2b-gate.pvl`), and the control C-NOGATE continues to the binding check instead.

Rust outcome: inside `finish_registration`, `decrypt_message_with_ratchet` (`beacon.rs:462-467`) returned `Some(decrypted)` with `decrypted.seq = t ≠ 1`, after which `beacon.rs:468-470` made the finish abort and return `None` (`:488-491`). On the fresh ratchet (r = 0, empty cache) Rust can open any t in 1..51 (`control.rs:223-245` with `RATCHET_MAX_GAP` = 50, `control.rs:7`); t = 0 is rejected before any open (`concrete.rs:264-274`).

Fields: `S` the pin (state), `B` the identity (state), `t` the opened sequence (local).

Finer than the API (`None`, V3) and coarser in range: the model covers t in 2..T_max only, and t in T_max+1..51 aborts without the witness. fs-registration collapses every t ≠ 1 into the abort without an open, which is exact for every other event. Used by A3 (witness) only.

### FsSent(dir, S, B, kid, root, t, m)

Model: one send step; the event precedes the output of the sealed frame.

Rust outcome, three cases:

- **Response, `server_to_beacon()`, t = 1:** the seal inside a successful build (`server.rs:471-479`), with `m = binding ‖ payload`. It is emitted only together with `FsServerCommitted`. A build that sealed and then failed (`server.rs:480-488`) returns `None`, discards its local ratchet and releases nothing; that is the drop branch.
- **Server tasking, `server_to_beacon()`, t ≥ 2 (stage P2):** a call `encrypt_message(bytes, kid)`, `encrypt_and_update(bytes, kid)` or `encrypt_and_update_json(bytes, kid)` on `obj`, with `kid` installed (`server.rs:225`, `:227`), that passed the empty-plaintext check (`ratchet.rs:421-423`) and the exhaustion check (`concrete.rs:133-144`; `control.rs:152-174`) and so allocated sequence t. The send counter became t and the send chain stepped before the seal (`concrete.rs:171-182`). Fields: `m` = `bytes` (arg), `kid` (arg), `B` = `pk_by_kid(kid)` (state), `S` = `identity_pk` (state), `t` (returned as `Encrypted.seq` when the call succeeds, and visible through `ratchet_status` in every case), `root` a ghost: the root of the build that installed `kid`.
- **Beacon record, `beacon_to_server()` (stage P3):** `Beacon::encrypt_message(bytes)` in `Established` that allocated sequence t (`beacon.rs:152-163`). Fields: `kid` = `identity_key_kid`, the frame's sender field (state, `beacon.rs:153`); `S` the pin; `B` the object's identity; `root` a ghost, the root of its finish.

Definition chosen: `FsSent` denotes the allocation of sequence t for plaintext m (the send attempt), not the `Some` return. After allocation the counter stays advanced even when the seal fails (`concrete.rs:206-209`; `ratchet.rs:440-443`), when `encrypt_and_update` cannot capture its snapshot after a successful seal (`server.rs:506`; the frame is then not returned), or when the JSON rendering fails (`server.rs:517`). Those calls return `None`, but the advance is visible through `ratchet_status` (`server.rs:207-209`; `beacon.rs:137-142`). The model step for such a call emits `FsSent` and outputs a frame that Rust never released. The model attacker therefore knows more than the Rust attacker, which is sound for S1 and S2, and the set of `FsSent` events is the same in both, which is exact for C1, C2 and UKSr. Under the alternative "returned `Some`" definition the model would contain `FsSent` events with no Rust counterpart, and C1 would only say "accepted only if sent or attempted". This settles the plan's remark that a failed seal is "observationally a dropped frame" at the level of events; the send relation itself is the pending L4.

Coarser or finer: (a) The plaintext is of the scenario's modelled form (E7). In s2b the registration payload is a fresh name, and each later tasking is either an attacker-chosen 8-byte prefix followed by a fresh name or, in the tasking form used by the authentication targets, a whole plaintext the adversary chooses ([Record-model forms](#record-model-forms-and-event-meaning)). (b) The attacker schedules the sends. (c) K_s bounds the number of sends, and `u64::MAX` exhaustion is unreachable. (d) An empty plaintext is refused before allocation (`ratchet.rs:421-423`) and emits no event, which is exact. (e) All record peers have the key ID `fs_kid(1)` (E5).

### FsReceived(dir, S, B, kid, root, t, m)

Model: a successful open in a receive step at t ≤ T_max, with the state variables updated as in Rust; and, at the Beacon, the t = 1 event at the finish commit. In the record scenarios every `FsReceived` is followed by its frame-carrying twin [FsReceivedFrame](#fsreceivedframedir-s-b-kid-root-t-frame).

Rust outcome, three cases:

- **Beacon, t = 1 at the finish:** the open inside a successful finish ([FsBeaconEstablished](#fsbeaconestablisheds-b-init-kid-root-ad-payload) (c)). It is counted only when the finish commits, because an open at sequence 1 followed by a binding failure aborts and discards the ratchet (E17). Fields: `m = binding ‖ payload` is local (`beacon.rs:472`): the finish returns only `Some(payload)` after stripping the binding (`beacon.rs:476-477`, `:509`) and returns no sequence; the binding is the encoding of `kid`, the response's key ID (arg) stored as `identity_key_kid` after the commit; `kid`, `S` and `B` as in the receive case below; `root` is local at the finish.
- **Beacon, `server_to_beacon()`, after establishment (stage P2):** `Beacon::decrypt_message(frame)` in `Established` returned `Some(Decrypted{plaintext: m, key_id: server kid, seq: t})` (`beacon.rs:164-174`; `ratchet.rs:499-536`). Success condition: nonempty input (`ratchet.rs:505-507`); exactly one complete frame with no trailing bytes (`ratchet.rs:347-357`, `:508-509`; `record.rs:17-23`); claimed sender equal to the pinned Server ID (`ratchet.rs:510-513`); ciphertext longer than the 80-byte overhead (`record.rs:35-61`); admission (`control.rs:223-245`) with either a cached lookup (`concrete.rs:270-280`; `refined.rs:317-382`) or a future derivation (`concrete.rs:282-389`); the CTX commitment (`ratchet.rs:456-469`; `record.rs:80-122`); and the AEAD open (`ratchet.rs:470-482`). State change: a cached t is swap-removed (`refined.rs:700-721`; `control.rs:415-461`); a future t sets r := t and caches r+1..t-1 (`refined.rs:755-778`). Fields: `kid` is the stored `identity_key_kid` (state); `S` the pin; `B` the identity; `root` a ghost; `t` and `m` are returned (`m` is V2).
- **Server, `beacon_to_server()` (stage P3):** `decrypt_message`, `decrypt_and_update` or `decrypt_and_update_json` on `obj` produced `ReceiveTransition::Accepted` (`server.rs:246-247`) for a frame whose claimed sender k is installed (`server.rs:237-245`). Fields: `kid` = k = `Decrypted.key_id` (ret), `B` = `pk_by_kid(k)` (state), `S` = `identity_pk` (state), `root` a ghost, the root of the build of k. The event is defined on the transition: the update and JSON wrappers panic instead of returning if rendering fails after the state change (`server.rs:273-274`, `:526-530`), a process-level failure outside the model (E18).

Failure (`None`): the complete entry ratchet state is preserved (`ratchet.rs:493-498`; `concrete.rs:429-431`, `:440-443`; `server.rs:44-52`). The model continues with the same state variables, or, after a failed open, stops the worker in the fail-stop form (E21).

Coarser or finer: (a) Frames above T_max go to the far branch (`FsFarAccepted`). (b) K_r bounds the attempts per peer direction. (c) The model gives every record peer `fs_kid(1)` and lets the attacker choose which worker receives a frame, whereas Rust routes deterministically on the claimed sender within the object the application calls (E5, pending L2). (d) On the Server the sender check at `ratchet.rs:511` always passes (expected = claimed, `server.rs:237`, `:246`); the routing lookup is the real check. (e) Codec-level rejections (empty input, trailing bytes, short ciphertext) are part of "does not parse" in the model.

### FsReceivedFrame(dir, S, B, kid, root, t, frame)

Model (record scenarios, added after the P2 review): emitted immediately after every `FsReceived`, with the same `dir`, `S`, `B`, `kid`, `root` and `t`; `frame` is the frame that the acceptance opened. At the finish (t = 1) it is the response's frame (`beacon.rs:462-467`); in a receive step it is the input of the receive attempt.

Rust outcome: the same call and outcome as the `FsReceived` it follows. Fields: as `FsReceived`, with `frame` in place of `m`; `frame` is the call argument (arg): the bytes passed to `decrypt_message`, or the response frame that `finish_registration` decoded from its argument (`beacon.rs:422-431`).

Witness only: it lets a witness say which frame was accepted, and it is used by C5c alone. ProVerif generates no clause for an event that a query does not mention, so it changes no other target. It adds nothing to the Rust reading of any security result (E24).

### FsFarAccepted(dir, S, B, kid, root, t)

Model (record scenarios): the far branch for t > T_max opened the frame with `ratchet_material(fs_far_chain(anchor, t))`, where the anchor is the chain at position T_max+1; the worker emits only this event and stops.

Rust outcome: as `FsReceived` (Beacon or Server receive case) with t > T_max. Rust admits it if and only if t ≤ r + 51 − |C|, where |C| is the number of cached keys (`control.rs:223-245`); it then sets r := t, caches the skipped keys (`refined.rs:755-778`) and returns the plaintext.

Coarser than Rust: nothing after a peer direction's first far acceptance is modelled, no `FsReceived` is emitted for it, no plaintext is recorded, and the far material comes from a model-only function rather than from iterating the chain (`concrete.rs:282-389`). This is owner decision OD4 and the pending L3. C4 shows that the branch never fires for honest sessions; for C1 and C3, coverage of a peer direction ends at its first far acceptance. Because the far material is model-only, a frame that an honest sender sealed above T_max under the real chain would be refused by the branch; within the s2b bounds no honest frame lies above T_max, and a stage that lets an honest sender go beyond T_max must raise T_max or derive the far material from the real chain, or C4 would hold for those frames by construction ([records guide step 8](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)).

### FsReceiveRejected(dir, S, B, kid, root, t, frame)

Model (record scenarios): a parsed frame with the expected sender whose receive attempt was rejected, in the rejection branches that the scenario names (see below; in `fs-records-s2b` an old uncached target, a failed cached open or a failed future open, and not a failed far open); the state is unchanged. The last field, added after the P2 review, is the refused frame.

Rust outcome: a decrypt call returned `None` after the frame decoded completely, its claimed sender equalled the expected sender (Beacon: the pinned Server ID; Server: an installed peer, after routing) and its ciphertext was longer than 80 bytes. The rejection came from admission (`concrete.rs:264-268`, `:270-274`, `:282-290`, or the defensive checks at `:322-378`), from the defensive rejection when the selected material is absent (`record.rs:81-84`, through `concrete.rs:404-422`), from the CTX commitment (`record.rs:115-122`; `ratchet.rs:456-469`), from an absent AEAD request (`record.rs:153-157`; `ratchet.rs:471`) or from the AEAD (`ratchet.rs:470-482`). The two defensive rejections cannot occur for a prepared receive of the core, which always selects present material. The entry state is preserved (`ratchet.rs:493-498`; `concrete.rs:429-431`, `:440-443`).

Fields: as `FsReceived`, with the refused frame (arg, the call's input) in place of `m`; `t` is the frame's claimed sequence (arg).

Finer than the API (V3); witnesses and controls only. Three limits matter for the claims that use it. First, after an acceptance at t, any parsed frame at t from the expected sender is rejected, a garbage frame as much as a replay of the genuine one (`concrete.rs:270-274` rejects both before any open), so a witness that is to show a replay refusal must name the frame. Until the P2 review the event carried no frame, and the review showed that the replay-rejected witness C5c was then satisfied by a garbage frame at sequence 1; the event now carries the refused frame, and C5c requires it to equal a frame that `FsReceivedFrame` records as accepted earlier by the same Beacon. Second, the fail-stop form (E21) ends a receive worker after a failed open, so it cannot express a claim whose traces need a failed open followed by a further receive (C5b, C-STALE, C-FAILMUT); a rejected old target is refused before any open and keeps the worker running in both forms, so claims that need only such rejections, C5c included, can be expressed in both. Third, a target may emit it only in the rejection branches its witness needs, to save memory; in that target the event means a rejection in those branches only, which leaves a reachability witness sound but limits an unreachability statement to those branches, and the target's documentation must name them (E22). `fs-records-s2b` emits it for every parsed frame from the pinned Server ID that is rejected at a target t ≤ T_max (an old target that is not cached, a failed cached open, a failed future open) and not for a failed far open ([records guide step 9](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)).

### Secrecy predicates

- **`attacker(x)`** (S1, S2, S3): the network adversary can compute the bytes `x` from every V1 output, every deployment constant (the Server identity key and ID, all public keys) and its own keys. It never sees a V2 value. Under OD2 and the no-reveal scope it never sees the Server identity secret, an honest Beacon's secrets, roots, chains, cached keys or snapshots.
- **`attacker(k)`** (the corruption disjunct of A2, R1', C2, S1 and S3-server): the adversary holds the Ed25519 secret behind `B`. In the model this holds exactly for identities the attacker built from public constructors; an honest Beacon's secret is a fresh name that is never output. Rust reading: `B` is not the identity of a Beacon object whose secret stayed private.
- **S1 at t = 1:** `m = binding ‖ payload`, and the binding is public, so `attacker(m)` amounts to the adversary learning the registration payload.
- **S3, `attacker(root)`:** `root` is never returned in readable form (the Server returns it only inside the opaque token), so S3 says that the network adversary cannot compute the 32-byte derived secret of the session.
- **SS1 (stage P5):** `choice[x0, x1]` as the plaintext of a Beacon send step. Rust reading: the application's plaintext is one of two adversary-chosen values, and the adversary sees only V1 outputs.
- **SS2 (stage P5), private announcement of `(kid, root)`:** no Rust counterpart. It is the definitional freshness gate of owner decision OD5, selecting the partnered Server peer by identical root; it must stay on a private channel and must not change any public behaviour of the protocol processes.

## Record-model forms and event meaning

The following model forms of the record scenarios change no event's definition; each changes which traces the model contains or how ProVerif searches them, and each needs the justification named.

- **v2, early fresh Server coins (E20):** see [FsServerAccepted](#fsserveracceptedobj-s-b-init-rid-root) (c). Trace-equivalent at one bundle per object; the justification is written in [records guide step 2](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications) and is not yet separately reviewed.
- **na, names without session arguments:** `new x[]` changes only ProVerif's internal abstraction of names, making it coarser, and not the process semantics; a TRUE verdict stays sound and a FALSE verdict still needs a reconstructed trace.
- **nx, the selection heuristic in `fs-common.pvl`:** changes only the order of resolution ([analysis](formal-verification-analysis.md#the-fs-selection-heuristic-nx)).
- **Application prefix (s2b):** the later taskings have the plaintext `registration_payload(prefix, m')` with an attacker-chosen 8-byte `prefix` and a fresh `m'`. Rust reading: an application tasking whose first 8 bytes are any value the adversary chooses, including a binding-shaped value, followed by fresh bytes. Without it the C-NOGATE mutant cannot fail, because a fresh name never parses as `binding ‖ rest`; C-NOGATE keeps it.
- **Attacker-input plaintexts (L6 item 4, E7):** stage P2 adds, in `fs-records-s2b-taskings-chosen.pvl`, a choice for each tasking between the fresh form and a whole plaintext that is an attacker input; the authentication targets A1, A2, C1, C3 and C4 run in that form, and S1, S4, the witnesses and the controls in the fresh form ([records guide step 5](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)). The planning text that follows is kept as the rule P3 applies to C2 and UKSr. Its `FsSent` then means a send of an adversary-chosen application plaintext. Such a step makes S1, S2 and UKSr false by construction. For S1 and S2 the attacker knows its own plaintext. UKSr links a Server receive to a Beacon send only through the plaintext, and the Server accepts records from a peer that the adversary registered (S4), so the adversary can seal the plaintext it chose for an honest Beacon's send on its own peer and obtain a receive with another identity. The secrecy targets and UKSr must therefore run without the step, or range only over a separate marker of fresh sends. If the step does not fit, the restriction is recorded instead: the authentication claims are shown for Rust runs in which every plaintext they mention consists of fresh application bytes (unique per send and unknown to the adversary when sent), preceded in s2b by an 8-byte prefix the adversary may choose.
- **Fail-stop (E21):** a failed open of a parsed frame ends the receive worker. It covers Rust runs up to the first failed open of each worker directly; runs with interleaved failures are reached by deleting the failed calls, which is sound only by failure neutrality (pending L3) and only for claims that do not mention `FsReceiveRejected`. It cannot express C5b, C-STALE or C-FAILMUT, whose traces need a failed open followed by a further receive; the replay-rejected witness C5c refuses an old target, which keeps the worker running, and can be expressed in both forms (records guide, fail-stop measurement). In s2b the fail-stop form was measured for C1, C3 and C4 but no target uses it, so no s2b result relies on E21; every s2b target runs in the failure-interleaving form, in which failures consume attempts inside the model.
- **Direction split (E19):** `fs-records-s2b` has no Beacon send worker and no Server receive worker, and `fs-records-b2s` has no Server send worker after the response and no Beacon receive window. The removed workers either output frames sealed under the other direction's chain, the second HKDF projection of the root (`crypto.pvl:72-80`), which the kept direction never uses, or touch only that direction's fields of the peer state (E16). For s2b the argument that removing them changes no claim of the kept direction is written in [records guide step 4](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications) and is not yet separately reviewed; for b2s it is a P3 item.

## Register of coarser and finer points

| Id | Point | Direction | Claims touched | Covered by |
| --- | --- | --- | --- | --- |
| E1 | Fields that Rust does not return: token, derived, local and ghost fields | Definitional | All | [Field kinds](#field-kinds); stated in the guide and the analysis document |
| E2 | Failure-cause events are finer than `None` | Finer | R2, R3, R5, A3, C5b, replay-rejected witness, C-FAILMUT | V3; never counted as security results |
| E3 | Every model Beacon pins `(S, SERVER_KEY_ID)`; Rust Beacons may pin any key and ID (`beacon.rs:59-83`), and bundles carry no Server field (`pqxdh.rs:314-319`) | Coarser (fewer Beacons) | A1, S3-beacon and the Beacon-side record claims (the record-form A1, C1, C3 and C4 in s2b, and S2); the b2s Server-side security claims (C2, C3, C4, UKSr, and A2 re-proved in b2s) | A2, R1' and S3-server are pin-free (P1). In s2b a Beacon outputs nothing after its bundle, so the P1 argument (the pin enters only the finish, which outputs nothing) carries over: A2 re-proved in s2b and the Server-side claim S1 are pin-free. A1, S3-beacon and the Beacon-side claims are about Beacons that pin the honest Server key (the threat model's compiled-in key). For the b2s Server-side claims, A2 re-proved in b2s included, Beacons send frames after a finish that depends on their pin, so the P1 argument does not apply and pin independence is open (P3). Witnesses need no pin independence: a model trace is a Rust trace whatever the other Beacons pin |
| E4 | Accept and build adjacent and on one object | Rescheduling | A1, A2, R1, R1', S3 | Pending L1 (i)-(v); case (iv) open |
| E5 | One registration per record object; all record peers share `fs_kid(1)`; the attacker routes frames to any worker | Merge, adds traces | C1-C5, S1-S4, UKSr | Pending L2 |
| E6 | `FsSent` is the allocation; the model releases a frame even when Rust's seal or snapshot fails | Exact for events; model attacker stronger | C1, C2, S1, S2, UKSr | [FsSent](#fssentdir-s-b-kid-root-t-m); pending L4 |
| E7 | Registration payloads and record plaintexts are fresh names (plus the s2b prefix); Rust allows any nonempty bytes, adversary-known or adversary-chosen ones included, and the registration default 0xFF | Coarser (restriction) | A1, C1-C3, UKSr; S1, S2 by intent | Registration: restriction recorded (guide step 6). s2b: the authentication targets also cover whole adversary-chosen taskings; the registration payload stays fresh, and S1 is about fresh tasking bytes ([records guide step 5](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)). b2s: P3 |
| E8 | `FsServerAcceptFailed` covers only the failure causes of the theory | Coarser | R5 only | Deletion argument ([FsServerAcceptFailed](#fsserveracceptfailedobj-s-b-rid)) |
| E9 | Far-target collapse above T_max | Coarser | C1, C3, C4 | OD4; pending L3 |
| E10 | Bounds K_reg, K_s, K_r, T_max | Coarser | All | Bounded results are the deliverable (OD1); arbitrary depth stays with the Lean side |
| E11 | The `Some`/`None` bit of receives and finishes is not published | Coarser for equivalence only | SS1, SS2 | P5 must publish it (V3) |
| E12 | Terms versus bytes | Idealisation | All | V4 |
| E13 | Wrong-state calls, accessors, key-management calls and test helpers are not modelled | Exact for wrong-state calls, public accessors and test helpers (no state change); key-management calls change the state and are covered by equivalence (a pre-drawn one-time key) or by trace removal (the deletions); secret accessors are excluded (reveals) | None | [Capabilities](#capabilities) |
| E14 | Finish later-open range: 2..T_max in s2b, collapsed in fs-registration | Coarser witness range | A3, C-NOGATE | [FsBeaconFinishOpenedLater](#fsbeaconfinishopenedlaters-b-t) |
| E15 | Two live Server objects with one identity; duplication by persistence | Per-object state | R1 and R1' are per object; R4 FALSE as expected | OD2; persistence out of scope |
| E16 | A peer's send and receive workers run in parallel, while Rust calls on one object are serial | Over-approximation (every serial order is an interleaving) | C1-C5, S1-S4, UKSr | Pending L1 product decomposition: sends touch the send counter and chain (`concrete.rs:171-182`), receives the receive counter, cache, chain and slots (`refined.rs:700-721`, `:755-778`), disjoint fields of `control.rs:64-68` and `refined.rs:57-62` |
| E17 | `FsReceived` at t = 1 is emitted at the commit, not at the open | Exact (an aborted finish discards the ratchet) | C1, C3 | [FsBeaconEstablished](#fsbeaconestablisheds-b-init-kid-root-ad-payload) |
| E18 | Wrapper panics after an accepted receive (`server.rs:273-274`, `:526-530`) | Outside the model | None | Process-level failure |
| E19 | Direction split | Removes processes | All record claims | s2b: argument written, not yet reviewed ([records guide step 4](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)); b2s: P3 |
| E20 | v2 early fresh Server coins | Reorder, trace-equivalent at one bundle per object | All record claims | Argument written, not yet reviewed ([records guide step 2](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)) |
| E21 | Fail-stop receive workers | Removes traces after a failed open | Claims that do not mention `FsReceiveRejected`, where used; not used in s2b | Pending trace-mapping argument (failure neutrality, L3) |
| E22 | `FsReceiveRejected` may be emitted only in selected branches, and until the P2 review it carried no frame | Weaker witness | C5b, replay-rejected witness (C5c), C-FAILMUT | [FsReceiveRejected](#fsreceiverejecteddir-s-b-kid-root-t-frame); in s2b emitted at t ≤ T_max only. Since the P2 review it carries the refused frame, and C5c ties that frame to one accepted earlier through `FsReceivedFrame` ([records guide step 9](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)) |
| E23 | One Server identity key and one `server_kid`: every model Server object uses `SERVER_IDENTITY_SECRET` and the own ID `SERVER_KEY_ID` (`fs-common.pvl:34-37`), whereas Rust objects may be built with any identity key and any `server_kid` (`server.rs:148-168`) | Coarser (fewer Servers) | A2, R1, R1', S3-server, S1 and the record claims; A1 and S3-beacon through the Beacon's pin | OD2 and the threat model's single compiled-in Server key (plan section 2.2 I): the Server-side readings are about Server objects with the modelled identity key and `server_kid`. No symmetry argument for other keys or IDs is made |
| E24 | `FsReceivedFrame` is a witness-only twin of `FsReceived` that carries the accepted frame instead of the plaintext (added after the P2 review) | Exact (same call, same emission points) | C5c only | [FsReceivedFrame](#fsreceivedframedir-s-b-kid-root-t-frame); no clause for other queries |

## Rust outcomes without an fs event

| Rust outcome | Location | Why no event is needed |
| --- | --- | --- |
| `get_shared_secret` returns `None` before the registration ID (decode, tag, key decode, signatures, `validate_init_kex`) | `server.rs:334-353` | No state change and no output; deleting the call is exact |
| `get_shared_secret` returns `None` after the status check for a cause outside the theory | `server.rs:361-414` | No state change and no output ([FsServerAcceptFailed](#fsserveracceptfailedobj-s-b-rid)) |
| `build_registration_response` returns `None` | `server.rs:434-488` | The token is consumed and nothing else changes: the model's drop branch |
| `finish_registration` returns `None` | `beacon.rs:403-406`, `:488-502` | In `InitSent` the Beacon aborts for good (the model process stops); in any other state nothing changes |
| `get_registration_bundle` returns `None` | `beacon.rs:301-357`, `:333` | No state change and no output |
| Encrypt returns `None` before allocation (empty input, unknown ID, Beacon not established, exhaustion) | `ratchet.rs:421-435`; `server.rs:225-227`; `beacon.rs:154-161` | No state change and no output |
| Decrypt returns `None` | `ratchet.rs:505-536`; `server.rs:237-249`; `beacon.rs:165-172` | The entry state is preserved; only the witness event `FsReceiveRejected` records it, and only for parsed frames from the expected sender |
| Key management and accessors | `beacon.rs:84-296`; `server.rs:173-212` | [Capabilities](#capabilities) |

## What the claims mean for Rust

Each reading below is a statement about Rust runs whose events project as above. It holds only within the stated bounds, only as a symbolic statement under V4, and only conditionally on this projection (L6, reviewed) and on the pending paper arguments: L1 and L5 for registration, and in addition L2, L3, L4 and the record-model items E19-E21 for records. For records it covers a peer direction only up to its first far acceptance. The P1 verdicts and their exact query lines are in the [P1 guide](impl/proverif-free-schedule-registration.md#claims-classes-and-bounds). The P2 verdicts and their exact query lines are in the [records guide](impl/proverif-free-schedule-records.md#claims-classes-and-bounds); the P3 targets are planned, and their exact query text is fixed when they land. Only security results count as evidence; definitional checks hold by construction, witnesses show that the events a claim speaks about occur, controls show that a cited Rust check is what makes a claim hold, and limitations document expected behaviour. Every "Server object" below is a Server object built with the modelled identity key and `server_kid` (E23), and every Beacon that "pins the honest Server key" pins that key and that ID.

### Registration (fs-registration, stage P1)

| Claim | Class | Rust reading |
| --- | --- | --- |
| A1 | security | Every Beacon object that pins the honest Server key and whose `finish_registration` returned `Some(payload)` is matched by its own, distinct successful `build_registration_response` on a Server object with the honest identity, which installed the Beacon's identity under the Beacon's stored `kid`, from the same root, with the same AD and the same verified key tuple (that of the accept whose token the build used), and with `data` equal to `payload`; in runs without later Server records and for fresh `data` |
| A2 | security | If `get_shared_secret` on some Server object with the modelled identity key and `server_kid` returned `Some` for identity `B`, then the adversary holds `B`'s secret, or a Beacon object with identity `B`, whatever key it pins, returned a bundle with exactly that verified key tuple and registration ID from `get_registration_bundle` |
| R1 | security | Among its first three `get_shared_secret` calls, one Server object with the modelled identity key and `server_kid` never returns `Some` twice for the same registration ID |
| R1' | security | Among its first three calls, one Server object with the modelled identity key and `server_kid` never returns `Some` twice for an identity whose secret the adversary does not hold, whatever the registration IDs, because such a Beacon returns at most one bundle (pending L5) |
| S3-server | security | The adversary cannot compute the root of a session that a successful build on a Server object with the modelled identity key and `server_kid` installed for an identity whose secret it does not hold |
| S3-beacon | security | The adversary cannot compute the root of a session that a Beacon pinning the honest Server key established |
| R2 | definitional | A replay rejection on an object follows an acceptance of that registration ID on the same object; holds by construction |
| R3 | witness | An honest Beacon's bundle, already accepted by an object, is refused with `None` by that object |
| R5 | witness | On one object a `None` after the status check (a DH refusal) is followed by `Some` for the same registration ID |
| W1, W2, W3 | witness | A Beacon completes with the first or the second key ID of an object; an object accepts a bundle of an identity whose secret the adversary holds |
| R4 | limitation | Two live objects with one identity both return `Some` for one honest bundle (OD2) |
| C-NOCHECK | control | If the consumed-set test (`server.rs:355-360`) were removed, R1 would fail |
| C-UKS | control | If the root input and the AD did not bind the Beacon identity, A1 would fail by an unknown-key-share |

### Server-to-Beacon records (fs-records-s2b, stage P2)

Bounds (K_s, K_r, T_max) = (2, 3, 3) with the far branch: after the sequence-one response the Server sends sequences 2 and 3, and the Beacon has three receive attempts from r = 1. The security results run at K_r = 3; the witnesses and controls run at the smallest K_r that exhibits them (1, 2 or 3), and every trace at a smaller K_r is also a trace at K_r = 3. "Chosen" marks the targets whose taskings may be whole adversary-chosen plaintexts; the others use fresh tasking bytes behind an adversary-chosen 8-byte prefix ([records guide step 5](impl/proverif-free-schedule-records.md#model-steps-and-their-justifications)). The verdicts, exact result lines, times and memory are in the [records guide](impl/proverif-free-schedule-records.md#claims-classes-and-bounds).

| Claim | Class | Rust reading |
| --- | --- | --- |
| A1 (record form, chosen) | security | As registration A1, now in runs where Server objects also send later taskings, with any adversary-chosen plaintexts or prefixes, to the new peer before or after the Beacon finishes. Together with A3 and C-NOGATE it covers the HB-95 class: a later genuine tasking never completes a registration, and the sequence-one gate (`beacon.rs:468-470`) is what prevents it |
| A2 (re-proved, chosen) | security | As registration A2, in the record process; pin-free (E3) |
| A3 | witness | A finish opens a later genuine frame (t in 2..T_max) before the gate aborts it, so the gate is really reached |
| C1 (chosen) | security | Every acceptance of sequence t with plaintext `m` by a Beacon that pins the honest Server key is matched by its own, distinct allocation of sequence t for `m` by a Server object on the peer installed for that Beacon (same `S`, `B`, `kid` and root), including in runs where rejected frames are interleaved, and whether the application's taskings are fresh or adversary-chosen; the registration payload is fresh (E7). The acceptance is either a `decrypt_message` call that returned `Some(Decrypted{plaintext: m, seq: t})`, or, at t = 1, a finish that returned `Some(payload)`, where `m = binding ‖ payload` is local and the binding encodes the stored `kid` |
| C3 (chosen) | security | One such Beacon object never returns `Some` twice for the same sequence, the finish's sequence 1 included, whatever the plaintexts |
| C4 (chosen) | security | No such Beacon accepts a frame above T_max within the bounds, so the far collapse never fires in s2b |
| C5a | witness | Out-of-order and cached acceptance occur: sequence 3, then the cached sequence 2 (expected FALSE correspondence "2 before 3") |
| C5b | witness | A rejected attempt at sequence t is followed by the acceptance of t, so a rejection leaves t acceptable (expected FALSE correspondence) |
| C5c (replay-rejected witness, K_r = 1) | witness | A frame that a Beacon accepted is passed to it again and refused with `None`: in the reconstructed trace the finish accepts the registration response frame at sequence 1, and the first `decrypt_message` call on the same frame refuses it as an old target that is not cached, without an open (`concrete.rs:270-274`). The receive events carry the frame (E22, E24), so the refused frame is the accepted one, not merely some frame at an accepted sequence |
| S1 | security | The adversary never computes a fresh registration payload or fresh tasking bytes that a Server object with the modelled identity key and `server_kid` allocated to a peer whose identity secret it does not hold; any adversary-chosen prefix is excluded from this reading; pin-free (E3) |
| S4 (s2b half) | witness | A peer registered by the adversary reads the tasking sent to it at sequence 2: the same Server code serves every identity |
| C-RETAIN | control | If a cached key were kept after a successful open (against `control.rs:415-461`; `refined.rs:700-721`), C1 and C3 would fail by replay |
| C-NOGATE | control | If the sequence-one gate (`beacon.rs:468-470`) were removed, A1 would fail by the later-record substitution; this mutant is the behaviour of `vcvio` |
| C-STALE | control | If a failed open restored the state from before the previous success (against `concrete.rs:440-443`), C3 would fail |
| C-FAILMUT | control (inverted) | If a failed open consumed its target or cached key, the C5b witness would become unreachable (at K_r = 2): keeping the entry state after a failure is what lets the genuine frame be accepted after a forgery |

### Beacon-to-Server records (fs-records-b2s, stage P3)

Bounds (K_s, K_r, T_max) = (2, 3, 2) with the far branch: each Beacon sends sequences 1 and 2, and each Server peer has three receive attempts from r = 0.

| Claim | Class | Rust reading |
| --- | --- | --- |
| C2 | security | Every record that a Server object accepted from the peer installed with identity `B` is matched by its own allocation of that sequence and plaintext by a Beacon with identity `B` in the same session, unless the adversary holds `B`'s secret |
| C3, C4 (b2s) | security | As in s2b, for Server peer receives; a far acceptance happens only at a peer whose identity secret the adversary holds |
| UKSr | security | A Server object never attributes a fresh record that a Beacon with identity `B2` allocated to a peer with another identity `B1` |
| S2 | security | The adversary never computes a fresh record plaintext of a Beacon that pins the honest Server key |
| S4 (b2s half) | witness | Records of a peer registered by the adversary are accepted by the same Server object |
| A1 (re-proved) | security | As registration A1, in the record process |
| A2 (re-proved) | security | As registration A2, in the record process; unlike in s2b its independence from the Beacon pins is open (E3, P3) |
| C-UKS (record form) | control | If the root input and the AD did not bind the Beacon identity, UKSr would fail |

### Strong secrecy (stage P5)

SS1 and SS2 read as in [Secrecy predicates](#secrecy-predicates). Their models must publish the `Some`/`None` bit of every receive and finish (E11).

## Changes from the P0 draft

The P0 draft (scratch, 2026-10-04) was checked line by line against `9e588c6`. Changes:

- Basis moved to `9e588c6`; the Rust sources are unchanged since `959cdab`, so every draft citation was re-checked rather than re-derived. Corrected ranges: the registration-ID method is `pqxdh.rs:195-204` and its hax replacement `:212-220`; `beacon_start` is `pqxdh.rs:304-321`; the bundle's absent Server field is shown by `pqxdh.rs:314-319`; `prepare_cached_receive` is `refined.rs:317-382`; `derive_root_key_input` is adapter `pqxdh.rs:46-59`; the `Decrypted` construction is `ratchet.rs:485-489`; the CTX check is `ratchet.rs:456-469`; the public accessors are listed without the secret ones they enclosed.
- `Encrypted.key_id` is the caller's target, not a frame field (V1).
- The uses of the consumed set are listed completely: construction and persistence (`server.rs:166`, `:278-299`) besides `server.rs:355`, `:361` and `:415`.
- The bindings drive a persistence wrapper (`BindingServer`) around the same `Server` calls; the draft did not mention the wrapper.
- `FsServerAcceptFailed` under `crypto.pvl` arises only from a prekey or one-time key that is not an X25519 public key, as P1 established; the draft also listed the identity conversion.
- Field kinds refined ([Field kinds](#field-kinds)): `kid` on Beacon receives is state and `rid` at the Beacon is derived; `root` at the build is a token field.
- Tier U (claims U1-U7) removed, following OD1.
- New register entries E19-E22 (direction split, v2, fail-stop, frame-less `FsReceiveRejected`), the record-model forms section, and the claim readings for the P2 decisions (C5 as FALSE correspondences, the replay-rejected witness, C-STALE, C-FAILMUT, UKSr in place of C-UKS on C2).

Status of the draft's review items:

1. `FsSent` as allocation: applied in P1 (now `fs-common.pvl:186-192`). The P2 send-step annotation should cite `concrete.rs:171-182` and `:206-209`, `ratchet.rs:440-443` and `server.rs:506`.
2. Pin-free A2 and R1': applied in P1; E3 records the remaining pin dependence.
3. `FsReceiveRejected` in `fs-common.pvl`: applied in P1 (now `fs-common.pvl:208-213`, with the frame field added after the P2 review).
4. Attacker-chosen plaintexts: recorded as a restriction for registration (guide step 6); open for records (E7).
5. Fields that Rust does not return: named in the P1 documentation, refined here.
6. The `Some`/`None` bit in the P5 equivalences: open (E11).
7. The failure causes of `FsServerAcceptFailed`: listed in P1 (now `fs-common.pvl:140-151`).
8. The s2b finish shape (open at 2..T_max, then the gate) wherever A3 or C-NOGATE runs: applied in P2 (`fs-records-s2b.pvl` with `fs-records-s2b-gate.pvl`).
9. Fidelity pins for the commit events citing both the core pin and the adapter pins: applied in P1 (`fs-registration.pvl:284`, `:330`).

## Review record

The separate L6 review that the plan requires was made at the start of stage P2 on commit `f381479` (Rust sources identical to `959cdab`, `533901f` and `9e588c6`). It re-read about 270 citations against the Rust sources, checked the eleven event mappings against the code, the P1 model and the P0 s2b generator, and confirmed the libsodium behaviour from the vendored libsodium sources. Verdict: approve with nits. Its findings and their resolution in this version:

1. An attacker-input send step would make UKSr false by construction, not only S1 and S2: [Record-model forms](#record-model-forms-and-event-meaning) now names UKSr.
2. A2 is re-proved in both record scenarios, but the b2s table lacked it, and the pin-free argument for it held only in s2b: the b2s table lists it, and E3 limits the pin-free statement to s2b and lists A2 in b2s under the open pin-independence item.
3. The list of Rust failures that `FsServerAcceptFailed` does not cover omitted the conversion of the Beacon identity at `server.rs:374`, which libsodium can refuse after the signatures verified: [FsServerAcceptFailed](#fsserveracceptfailedobj-s-b-rid) lists it and says that "cannot fail" is a property of `crypto.pvl`; guide step 7 matches.
4. The single Server identity key and `server_kid` had no register entry: E23 records it, and the Server-side readings name it.
5. Nits on field kinds and Rust facts: the Server-side `ad` is local at the build and derived on record calls; `Occupied` cannot come from a restored state, and ID exhaustion is reachable at the first build when `server_kid = u64::MAX`, so the model assumes `server_kid + K_reg <= u64::MAX`; the C1 reading and the t = 1 case of `FsReceived` say that the finish returns only the payload; `root` is never returned in readable form.
6. Nits on citations and wording: the secret-accessor ranges are split, E13 distinguishes key-management calls, `FsReceiveRejected` lists the two defensive rejections, and the ghost-field sentence matches the analysis document.

### Changes after the L6 review

The P2 review (three reviews of the s2b model, after this reference had been reviewed) led to the following changes here. None of them is reviewed yet as part of L6.

- `FsReceiveRejected` gained the refused frame as its last field, and the witness-only event `FsReceivedFrame` was added ([FsReceivedFrame](#fsreceivedframedir-s-b-kid-root-t-frame), E22, E24), so that the replay-rejected witness C5c shows a genuine replay refusal at K_r = 1.
- The statements that the fail-stop form cannot express the replay-rejected witness were wrong: it ends a worker only after a failed open, and C5c needs only the refusal of an old target.
- [FsReceiveRejected](#fsreceiverejecteddir-s-b-kid-root-t-frame) no longer says that every record scenario emits it for a failed far open; `fs-records-s2b` does not.
- [FsServerAccepted](#fsserveracceptedobj-s-b-init-rid-root) no longer calls the record scenarios' order the Rust order without naming the v2 draw, and points to the written v2 argument.
- The `fs-common.pvl` line citations are updated to the current file.

## Open items

- E7 for the b2s records (P3): the attacker-input send step for C2 and C3 or a recorded restriction, keeping S2 and UKSr free of attacker-input sends.
- E3 for the b2s Server-side security claims, A2 re-proved in b2s included (P3); the review of the arguments for E19 (s2b) and E20 written in P2; the review of the event changes made after the L6 review ([Changes after the L6 review](#changes-after-the-l6-review)); the b2s half of E19 (P3); and E21 if P3 uses fail-stop.
- The paper arguments L1 (including case (iv)), L2, L3, L4 and L5.
- Stage P4: an event that distinguishes the all-zero check from a DH refusal. Stage P5: the `Some`/`None` bit.
