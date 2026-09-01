# Summary of changes for run acaee272-2489-4875-ab7a-0f0140f44cfe
I replaced the blanket `import Mathlib` in the ideal models with the minimal imports they actually need, and kept the project building `sorry`-free with only the standard axioms.

What changed:

- `BeaconcryptCore/Model/Pqxdh/Primitives.lean`: `import Mathlib` → `import Mathlib.Data.Nat.Notation` (only the `ℕ` notation is needed; everything else in the file rests on Lean core / Batteries `List` lemmas, `simp`, `decide` and `omega`). The one `norm_num` step in `LE64_inj` was redundant after the preceding `simp` and was dropped, so `omega` closes the goal directly.
- `BeaconcryptCore/Model/Ratchet.lean`: `import Mathlib` → `import Mathlib.Logic.Function.Iterate` (needed for `f^[n]` in `chainAt`). Two order lemmas were specialised to `Nat.le_refl` / `Nat.le_trans`, `List.mem_of_mem_filter` to `List.mem_filter.1 _ |>.1`, and `List.Nodup.append` to the core `List.nodup_append`, which removes the dependency on `Mathlib.Data.List.Nodup`. The unused `open scoped BigOperators` / `open scoped Nat` lines were removed.
- `BeaconcryptCore/Model/Pqxdh/Theorems.lean`: added the single small import it needs for the `split_ifs` tactic (`Mathlib.Tactic.SplitIfs`), which it previously got by accident through the blanket import.
- `BeaconcryptCore/Model/Pqxdh/Runs.lean` and `Acceptance.lean`: the few generic-order / `norm_num` uses replaced by their `Nat`/core counterparts (`Nat.le_refl`, `Nat.le_trans`, `decide`).
- `BeaconcryptCore/Main.lean` (an empty scaffold whose only content was `import Mathlib`, some scoped opens and default `set_option`s) was deleted, as you chose; nothing referenced it.

No theorem statements were weakened or removed — only proof internals and imports changed.

Effect on build cost, measured with `lake build BeaconcryptCore`: the full project went from 8878 build jobs to 1741, and the two model files now build against tiny import surfaces on their own (98 jobs for the ratchet model, 67 for the PQXDH primitives, versus 8878 before). The remaining cost is the extraction/refinement layer, which pulls in Aeneas (that dependency itself imports a bounded part of Mathlib, not all of it). A full rebuild of the project's own modules now takes about 70 seconds here.

Verified afterwards: the whole project builds successfully from a cleared project build directory, contains no `sorry`/`admit`/`axiom`, and spot-checked theorems (`Ratchet.RecvWf.recvStep`, `Pqxdh.LE64_inj`, `Pqxdh.ServerWf.serverEmit`) depend only on `propext` and `Quot.sound`.


# Summary of changes for run 46f23e64-689c-46f1-8a9c-711118f953d1
I proved that the generated (extracted) PQXDH code refines the handwritten ideal model, and left the whole project building with no `sorry` and only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

What "refines" means here: the extracted PQXDH layer is cryptography-free — the primitives sit outside it, so the generated transitions are driven by values the caller supplies (the four X25519 contributions and the ML-KEM shared secret, the replay verdict, the key-identifier availability verdict, the authenticated sender identifier and the authenticated key-identifier binding). Each refinement theorem therefore says: if the generated inputs abstract (via `absBytes`, lifted by `absBinding`, `absVerified`, `absDHs`) to the values the ideal model computes over the abstract `Pqxdh.Crypto` interface, then the generated transition returns exactly the ideal outcome — the same acceptance or the same rejection, and on acceptance the same identifier, published data and surviving state.

New work, in `BeaconcryptCore/Refinement/`:

- `PqxdhProtocol.lean` — transition-level refinement:
  - `beacon_start_refines`: the generated bundle builder emits exactly the payloads the ideal `Pqxdh.beaconInit` signs (spec §5).
  - `validate_init_kex_refines` and `honest_bundle_validates`: the generated parser agrees with `Pqxdh.validateInit`, and an honest bundle is validated identically on both sides (§6).
  - `serverRegister` (driver composing `server_accept` → `server_prepare_commit` → `server_commit`) and `serverRegister_refines`: agrees with `Pqxdh.serverRespond` in all five outcomes the extracted core can express — replay, all-zero contribution, exhausted counter, identifier collision, and success with the ideal identifier, peer entry and associated data (§6–§14).
  - `beaconFinishDriver` (composing `beacon_prepare_finish` → `authenticate_registration_key_id_binding` → `beacon_commit`) and `beaconFinishDriver_refines`: agrees with `Pqxdh.beaconFinish` in all five outcomes — pinned-identity mismatch, all-zero contribution, wrong authenticated sender, key-identifier mismatch, and success (§15–§18).
  - `server_abort_candidate_refines`, `beacon_abort_init_refines`: the generated rollbacks are the ideal transactional rollback and the ideal abort.
- `PqxdhSession.lean` — session-level capstone: `GenHonestRun h` bundles the generated data of one honest registration plus the assumption that it abstracts to the ideal honest run `h`, and `honest_run_refines` composes the four transition results: the generated pipeline runs end to end without a rejection and yields the identifier, the published peer (identity key and associated data) and the pinned binding of the ideal run, while the ideal run takes exactly its two steps `serverStep` and `beaconStep`.

Also: the root module `BeaconcryptCore.lean` now imports the PQXDH refinement, so the complete proof surface is reachable from it, and `PQXDH_REFINEMENT.md` indexes the spec sections against the refinement theorems. `ARISTOTLE_SUMMARY.md` was read but not modified. The record layer (sealing/admitting the first server record) is not part of the extracted PQXDH module — it is the symmetric ratchet, whose refinement already existed in the project; in the PQXDH proofs it enters through the values fed back into the beacon transition.

# Summary of changes for run 4ef8ccba-e338-4ef9-bee5-2fd8f3a74ab9
I continued the ideal (symbolic) model of the BeaconCrypt modified PQXDH registration protocol from `pqxdh_spec.md`, extending it in four directions. The whole project builds with no `sorry`, no added axioms, and every new theorem depends only on Lean's standard axioms.

**New: the record layer provably commits** (`BeaconcryptCore/Model/Pqxdh/Commit.lean`). The transmitted ciphertext `CT ‖ T ‖ T*` determines the message key, the nonce, the associated data, the wire sequence number and the sender identifier (`openRecord_committing`, `ctxCommit_context_eq`), so a record cannot be re-labelled: sealed at one sequence number or under one sender, it does not open at another (`openRecord_relabelled`, `openRecord_wrong_seq`, `openRecord_wrong_sender`). Care was taken over the hash assumption: a global injectivity assumption on BLAKE2b-512 would contradict its fixed 64-byte digest length and make every consequence vacuous, so the assumptions are stated only about the pair of record contexts at hand (`NoCtxCollision`, `CtxDistinct`), together with the field lengths the protocol maintains (`RecordWf`).

**New: what the beacon's acceptance test rules out** (`Acceptance.lean`). The honest first record presented at any sequence number other than the one it was sealed at makes the beacon abort with `BadRecord`, and so does a record sealed for a different session — even though beacon acceptance is defined through the general receive-ratchet transition rather than a `seq = 1` test, as the specification requires.

**New: non-vacuity of those hypotheses** (`InstanceCommit.lean`). A concrete instance of the primitive interface is exhibited in which distinct record contexts provably commit to different values whenever their sequence numbers or senders differ, and every hypothesis of the beacon rejection result is discharged on a concrete honest run.

**New: whole runs of both parties** (`Runs.lean`). For the server: the allocation invariant `ServerWf` (every published identifier is at most the counter, none published twice) holds initially and is preserved by every registration, so the key-identifier collision check never fires on state the server itself produced, published peers survive unchanged under their identifiers across arbitrarily many further registrations, the consumed set and counter only grow, and a beacon bundle is served at most once for the lifetime of the server. For the beacon: `beaconRun` feeds a beacon a sequence of responses and at most one of them can be accepted, because leaving `InitSent` is irreversible and no other state ever accepts.

**Also**: the beacon state machine now includes the specification's `FreshWithCoins` state (a one-time X25519 key pregenerated through the compatibility API), with the corresponding initiation result, and `PQXDH_IDEAL_MODEL.md` — the section-by-section index from specification to Lean declaration — has been updated to cover all of the above. The new modules are reachable from the maintained root `BeaconcryptCore.lean`.


# Summary of changes for run 5ff6d781-c1a2-406a-b18c-b99f54bce80a
I built an ideal (symbolic) model of the modified PQXDH registration protocol from `pqxdh_spec.md` in Lean 4, in five new files under `BeaconcryptCore/Model/Pqxdh/`, reachable from the root module `BeaconcryptCore.lean`. The whole project builds with **no `sorry`**, no added axioms, and all theorems depend only on Lean's standard axioms.

**Model structure**
- `Primitives.lean` — byte strings, little-endian 64-bit encoding, the two HKDF info strings as explicit byte sequences, the signature/X25519/ML-KEM role tags with their parsers and domain-separation lemmas, and `Pqxdh.Crypto`: the parametric interface for Ed25519 attached signatures, Ed25519→X25519 conversion, X25519, ML-KEM-768, HKDF-SHA-512, detached ChaCha20-Poly1305 and BLAKE2b-512, with their ideal correctness and output-length assumptions.
- `Kdf.lean` — the PQXDH input keying material, root secret, associated data, the two directional chains, and the committing record layer (76-byte key/next-chain/nonce partition, CTX commitment, wire format `CT ‖ T ‖ T*`), packaged as an instance of the project's existing verified symmetric ratchet.
- `Protocol.lean` — wire types and the two state machines: beacon (`Fresh → InitSent → Established/Aborted`) and server (consumed-RID set, key-identifier counter, peer map), with `beaconInit`, `validateInit`, `serverRespond`, `beaconFinish`.
- `Theorems.lean` — the behavioural properties.
- `Instance.lean` — a deliberately insecure toy instance satisfying every assumption, plus a concrete honest run whose side conditions are checked by computation, showing the results are not vacuous.

**Properties proved** include: one-shot registration on both sides (a beacon that has sent its bundle cannot restart; a replayed bundle is always rejected as a registration replay); role-tag separation (a bundle with prekey and one-time-key tags swapped is rejected even though both signatures verify); replay consumption ordering (the registration identifier is consumed before response construction, so a failed attempt cannot be retried); transactional peer publication (a failed response construction leaves the counter and peer map untouched); key-identifier exhaustion and collision errors; empty-application-message rejection; pinned server-identity and authenticated-sender checks; all-zero-DH rejection; terminal abort semantics and the drop of registration-local key material on leaving `InitSent`; equality of the beacon's and server's four X25519 contributions; and, for an honest run, agreement on the root secret, the associated data, the complementary directional chains, the assigned key identifier, and delivery of the initial application message.

Also included: `PQXDH_IDEAL_MODEL.md`, an index mapping each specification section to the corresponding Lean declarations, and an incidental fix of stale module imports that were preventing the project from building at the start.

All work is committed and pushed, and the Properties table reflects the final state of the sources.

# Refinement summary for run efb23f7b-df1d-4784-8c84-6d93808cd65a and the later bound correction
The original run established the refinement structure summarized below. The repository later updated the production planner and proof so the production and ideal models share the exact 50-skipped-key boundary. The current whole project builds `sorry`-free.

**What was proved** (all in `BeaconcryptCore/Refinement/RatchetRefinement.lean`, which imports the handwritten model in `BeaconcryptCore/Model/Ratchet.lean` and the previously verified generated control plane in `BeaconcryptCore/Refinement/RatchetControl.lean`):

- `receiveMessage` — the generated receive logic assembled into one transactional step. A cached target follows plan → lookup → finish. A future target plans the gap, derives and caches only the skipped keys with `advance_receive`, advances the separately consumed target with `advance_receive_target`, and commits that private candidate only when authentication succeeds.
- `Refines` — the refinement relation: the concrete control-plane state represents an abstract receive state of the handwritten ratchet (receive counter = next expected index, with wire sequence number = abstract index + 1; the abstract chain key and every stored key are the ones derived from the session chain key; the cache holds exactly the sequence numbers of the abstract skipped keys).
- **`receiveMessage_refines`** (main result): for every positive wire target and every authentication verdict, if the concrete state represents the abstract state, then the generated step returns exactly the outcome of the handwritten receive step (delivered / replay / too-many-skipped / auth-fail) and its resulting state again represents the resulting abstract state. All four outcome branches are covered; wire sequence zero is covered separately by the state-neutral non-delivery theorem.
- The generated receive driver refines the handwritten `Ratchet.recvStep` directly at its bound of 50 skipped keys.
- `advance_send_refines`: the send path refines the handwritten sender.
- `receiveMessage_state_neutral`: on every non-delivery the generated step returns the state it was given unchanged, matching the state neutrality of the handwritten model.

**The boundary now agrees exactly.** The generated planner charges only retained skipped keys against the 50-entry cache. It derives and consumes the incoming target separately, so a future receive may retain exactly 50 skipped keys without reserving a fifty-first slot. The main theorem is stated directly against the handwritten `Ratchet.recvStep` with `maxSkip = 50`.

Current verification: the repository-locked `verify-lean` target regenerates the extracted modules and builds the maintained root successfully, while the Lean policy gate rejects `sorry`, `admit`, `axiom`, and `sorryAx` in repository-owned proofs.

# Summary of changes for run 2849bf9c-3c8a-42ca-8b3d-2e3fd6349746
I formalized and fully proved a symmetric single ratchet in Lean 4 (Mathlib), in the new file `RequestProject/Ratchet.lean` (~550 lines). The referenced `doc/` directory was not present in the uploaded project, so — as you confirmed — I worked from the standard symmetric-key (chain-key) ratchet model.

**The model** is parametric in its cryptography (`Ratchet.Crypto`): a chain-key KDF `kdfChain`, a message-key KDF `kdfMsg`, and an authenticated encryption scheme `enc`/`dec` with associated data, where `dec` returning `none` models an authentication failure. The only assumed property is decryption correctness. The sender state holds a chain key and a message counter; the receiver state holds a chain key, the next expected index, and a store of skipped message keys. `maxSkip = 50`.

**Receive-path design**: a message whose key is already stored is trial-decrypted with that key; otherwise indices before the next expected one are rejected as replays, a message whose acceptance would push the outstanding skipped keys past 50 is rejected, and otherwise the message key is derived and the ciphertext is *authenticated first*, before any state is written.

**What is proved (all sorry-free, standard axioms only):**
- *State neutrality* — on any rejection, including authentication failure, the receiver state is returned bit-for-bit unchanged (`recvStep_state_neutral_of_error`), and in particular no skipped keys are added or removed (`recvStep_authFail_no_new_skipped`). This covers messages that would otherwise have triggered skipping: the chain is not ratcheted and no keys are stored.
- *Exhaustive receive behaviour* (`recvStep_cases`): every message is either delivered from the store, delivered by ratcheting forward, or rejected with the state unchanged.
- *The 50-message bound* — the skipped-key store never exceeds 50 entries (`recvStep_skipped_length_le`), receive preserves the state invariant (`RecvWf.recvStep`), and a message needing more skips is rejected (`recvStep_reject_tooManySkipped`, with the 51-skip instance `recvStep_reject_51`).
- *Correctness* — in-order round trip (`recvStep_of_sendStep_inOrder`), accepting a message that skips k ≤ 50 messages while storing the intervening keys (`recvStep_skip_ahead`), and later out-of-order delivery of a skipped message from the store, with its key then removed (`recvStep_delivers_skipped`).
- *Replay rejection* (`recvStep_replay_rejected`).
- *Whole-session results* — a receiver started in sync stays in sync over an entire message stream (`recvRun_inOrder_state`) and decrypts every message to the sender's plaintext (`recvRun_inOrder_ok`).

To show the model is not vacuous, the file ends with a concrete toy instantiation of the primitives and machine-checked examples exercising each branch: in-order delivery, skipping, later delivery of a skipped message, rejection at 51 skips, forged-ciphertext rejection with unchanged state (both on the chain path and the stored-key path), and replay rejection.

The project builds cleanly with no `sorry`, no added axioms, and no linter warnings.
