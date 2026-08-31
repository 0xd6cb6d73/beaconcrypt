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
