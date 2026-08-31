# Ideal model of the BeaconCrypt modified PQXDH registration protocol

This document indexes the Lean formalisation of `pqxdh_spec.md`.  The model lives in

```
BeaconcryptCore/Model/Pqxdh/
├── Primitives.lean   -- byte strings, LE64, domain strings, key encodings, the primitive interface
├── Kdf.lean          -- PQXDH transcript and root secret, associated data, chain split, record layer
├── Protocol.lean     -- wire messages, both principals' states, the four transitions
├── Theorems.lean     -- the behavioural properties, including the honest agreement relation
├── Commit.lean       -- the record layer is key- and context-committing
├── Acceptance.lean   -- what the beacon's acceptance test rules out
├── Runs.lean         -- the server over a whole sequence of registrations
├── Instance.lean     -- a concrete instance of the primitive interface (non-vacuity)
└── InstanceCommit.lean -- an instance witnessing the commitment hypotheses
```

and is reachable from the maintained root `BeaconcryptCore.lean`.  The whole project
builds with no `sorry` and no added axioms; the results depend only on `propext`,
`Classical.choice` and `Quot.sound`.

The model is *ideal*: it is parametric in the cryptographic primitives
(`Pqxdh.Crypto`), which are assumed only to be correct (signature verification,
Ed25519→X25519 conversion agreement, X25519 agreement, ML-KEM correctness, AEAD
correctness) and to have the stated output lengths.  It makes no computational
security claim.

The record layer is not re-invented: it is an instance `Pqxdh.ratchetCrypto` of the
project's already verified handwritten symmetric ratchet
(`BeaconcryptCore/Model/Ratchet.lean`), so the server's first record is one
`Ratchet.sendStep` and the beacon's acceptance is one `Ratchet.recvStep` — i.e. "a
valid admissible initial receive-ratchet record" in the sense of spec §16, not an
`seq = 1` special case.

## Specification section → Lean declaration

| Spec | Content | Lean |
| --- | --- | --- |
| §2 | parties and long-term state | `Pqxdh.ServerState`, `Pqxdh.BeaconState`, `Pqxdh.ServerBinding`, `Pqxdh.Peer` |
| §3 | primitives, `HKDF₅₁₂`, `INFO_PQ`, `INFO_R` | `Pqxdh.Crypto`, `Pqxdh.INFO_PQ`, `Pqxdh.INFO_R` (lengths 46 / 41, and distinct) |
| §4 | `Tag_sig`, `Tag_X`, `Tag_PQ`, role bytes | `Pqxdh.tagSig`, `Pqxdh.tagX`, `Pqxdh.tagPQ`, lengths 33 / 34 / 1185, and the domain-separation lemmas |
| §5 | authenticated `InitKex`, `Fresh → InitSent` | `Pqxdh.initKexOf`, `Pqxdh.beaconInit`, `beaconInit_fresh`, `beaconInit_freshWithCoins` (pregenerated one-time key), `beaconInit_initSent` (no second bundle) |
| §6 | server validation, `RID = IK_B ‖ OT_B`, replay | `Pqxdh.validateInit`, `Pqxdh.ValidInit.rid`, `serverRespond_replay` |
| §7 | the four X25519 contributions, all-zero rejection | `Pqxdh.serverDHs`, `Pqxdh.dhNonZero` |
| §8 | 192-byte transcript, root secret, consumption | `Pqxdh.pqxdhIKM`, `Pqxdh.rootSecret`, `serverRespond_consumes` |
| §9 | associated data (153 bytes, server first) | `Pqxdh.assocData`, `assocData_length`, `assocData_inj` |
| §10 | `L ‖ R = HKDF(DS, INFO_R, 64)`, complementary chains | `Pqxdh.rootChains`, `HonestRun.chain_agreement` |
| §11 | checked key-ID allocation | `serverEmit_exhausted`, `serverEmit_collision`, `ServerWf`, `serverEmit_no_collision_of_wf` |
| §12 | `LE64(kid) ‖ M`, default `FF`, empty message rejected | `Pqxdh.LE64`, `LE64_inj`, `serverRespond_empty_app` |
| §13 | `key ‖ next_chain ‖ nonce`, AEAD + CTX commitment, `CT ‖ T ‖ T*` | `Pqxdh.nextChain`, `Pqxdh.msgMaterial`, `Pqxdh.ctxCommit`, `Pqxdh.sealRecord`, `Pqxdh.openRecord`, `Pqxdh.ratchetCrypto` |
| §13 | the commitment binds key, nonce, AD, tag, sequence and sender | `ctxCommit_context_eq`, `openRecord_committing`, `openRecord_relabelled`, `openRecord_wrong_seq`, `openRecord_wrong_sender` |
| §14 | `KexResponse`, transactional commit | `Pqxdh.KexResponse`, `Pqxdh.serverEmit`, `serverEmit_ok`, `serverEmit_failure_state`, `serverRespond_peers_preserved`, `serverRun_peers_preserved` |
| §15 | beacon decapsulation, pinning, role-reversed DHs | `Pqxdh.beaconFinish`, `Pqxdh.beaconDHs`, `beaconFinish_identity_mismatch` |
| §16 | record admission, sender check, `LE64(kid)` binding | `Pqxdh.beaconFinish`, `beaconFinish_bad_sender`, `HonestRun.beaconStep`, `HonestRun.beacon_rejects_reordered_record`, `HonestRun.beacon_rejects_foreign_record` |
| §17 | establishment, registration keys unavailable | `BeaconState.established`, `BeaconState.regSecrets`, `beaconFinish_drops_registration_keys` |
| §18 | failure semantics, one-shot | `beaconFinish_aborted_of_error`, `beaconFinish_not_initSent`, `serverRespond_replay_after` |
| §19 | honest agreement | `beaconDHs_eq_serverDHs`, `HonestRun.serverStep`, `HonestRun.beaconStep`, `HonestRun.keyId_agreement`, `HonestRun.ad_agreement`, `HonestRun.chain_agreement`, `HonestRun.app_delivered` |
| §20 | state-transition summary | the two transition functions and the theorems above |
| §6, §20 | one registration per bundle over a whole server run | `Pqxdh.serverRun`, `serverRun_replay_of_consumed`, `serverRun_served_at_most_once`, `ServerWf.serverRun` |
| §18, §20 | one accepted response over a whole beacon run | `Pqxdh.beaconRun`, `beaconFinish_result_not_initSent`, `beaconRun_accepts_at_most_once` |
| §21.3 | prekey and one-time role tags not interchangeable | `parseXTag_otk_tagX_pre`, `parseXTag_pre_tagX_otk`, `validateInit_swapped_roles` |

## The honest run

`Pqxdh.HonestRun` bundles the inputs of one honest registration (both parties' keys,
the server's ephemeral and ML-KEM randomness, the initial application message) and
names every derived value (`ds`, `ad`, `chains`, `kid`, `response`, `peer`,
`server'`, `beaconEstablished`, …).  `Pqxdh.HonestRun.Ok` collects the five side
conditions: fresh `RID`, no degenerate X25519 contribution, counter not exhausted,
proposed identifier free, non-empty application message.  Under `Ok`:

* `serverStep` — the server emits exactly `response` and commits exactly `server'`;
* `beaconStep` — the beacon accepts, ends in `beaconEstablished`, and returns `kid`;
* `keyId_agreement`, `ad_agreement`, `chain_agreement`, `app_delivered` — the
  agreement relation of spec §19.

`Pqxdh.Toy.demo` is a concrete such run over `Pqxdh.Toy.toyCrypto`, with
`Pqxdh.Toy.demo_ok` discharging `Ok` by computation, so the honest results are
instantiated at least once.

## The record layer commits (spec §13)

`Commit.lean` proves that the transmitted ciphertext `CT ‖ T ‖ T*` determines the
message key, the nonce, the associated data, the wire sequence number and the sender
identifier: `openRecord_committing`.  Consequently a record cannot be re-labelled
(`openRecord_relabelled`, `openRecord_wrong_seq`, `openRecord_wrong_sender`), and at
the level of the beacon transition the honest first record is rejected when presented
at another sequence number or for another session (`Acceptance.lean`).

The hypotheses about BLAKE2b-512 are deliberately *local*: `NoCtxCollision` says the
two commitment inputs at hand do not collide, and `CtxDistinct` says the two contexts
commit to different values.  A global injectivity assumption would contradict the
fixed 64-byte digest length asserted by `Crypto.blake2b_length`, and everything
derived from it would be vacuous.  `InstanceCommit.lean` exhibits an instance
(`Toy.tailCrypto`) in which `CtxDistinct` provably holds for contexts with different
sequence numbers or different senders, and discharges every hypothesis of the beacon
rejection result on a concrete run (`Toy.demoTail_rejects_reordered_record`).

## The server over a whole sequence of registrations (spec §11, §14, §20)

`Runs.lean` lifts the single-step results to `serverRun`, the server serving a list of
registration requests.  The allocation invariant `ServerWf` (every published
identifier is at most the counter; no identifier published twice) is established by an
empty server and preserved by every step, so the collision check of §11 never fires on
state the server itself produced (`serverEmit_no_collision_of_wf`), published peers
survive unchanged under their identifiers (`serverRun_peers_preserved`), the consumed
set and the counter only grow, and a bundle is served at most once for the lifetime of
the server (`serverRun_served_at_most_once`).

The same file treats the beacon side: `beaconRun` feeds a beacon a whole sequence of
responses, and `beaconRun_accepts_at_most_once` shows at most one of them can be
accepted, because leaving `InitSent` is irreversible
(`beaconFinish_result_not_initSent`) and no other state ever accepts a response
(`beaconRun_all_error_of_not_initSent`).
