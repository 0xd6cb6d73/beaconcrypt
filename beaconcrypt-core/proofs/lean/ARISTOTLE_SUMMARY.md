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