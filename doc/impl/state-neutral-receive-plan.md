<!-- SPDX-License-Identifier: 0BSD -->

# State-neutral receive implementation plan

## Status and baseline

This document is an implementation specification for the `proof` branch at commit `ff12e813a1f4b7ee6f6e86db573dc796eb1d7154`. It describes required future work and does not record completed behavior.

The implementation MUST make every normally returned receive rejection exactly state-neutral. A rejected frame MUST leave the volatile protocol state unchanged, and a rejected operation through `PersistentServer` MUST additionally leave the current `SnapshotHead`, stored snapshot bytes, generation, and store CAS count unchanged. A successful receive MUST continue to consume exactly one target receive key, retain the required skipped keys for out-of-order delivery, and withhold plaintext from a persistent caller until the resulting server snapshot has won the trusted-store CAS.

## Objective

For any live receive state `S` and input frame `F`, the normal-return contract is:

```text
receive(S, F) = (S, None)                  when F is rejected
receive(S, F) = (S', Some(plaintext))      when F is accepted
```

The equality in the rejection branch is complete state equality, not equality of selected counters. It covers the send and receive counters, both live chains, receive-cache length and order, every cached sequence tag and key/nonce value, the selected peer and all other peers, registration replay state, identities, and associated data. For `PersistentServer`, it also covers the local head, authoritative store contents, generation, and poison flag. The absence of a CAS invocation is an execution effect enforced with test-store call counting, not an application-metric claim. Other external metrics, logging, timing, rate-limit state, allocator behavior, and primitive-library side effects are outside this protocol-state equality and MUST NOT be stored inside the ratchet transaction.

The successful branch MUST publish one indivisible logical result: the receive chain advances through the target, every skipped key is cached once, the authenticated target key is consumed rather than cached, replay of that target is rejected, and the returned plaintext corresponds to the same target material and frame context used by the open callback.

## Current behavior and root cause

The current production path is `Server::decrypt_message` or `Beacon::decrypt_message`, then `decrypt_message_with_ratchet`, then `concrete_open_and_finish`, then `refined_open_and_finish`. The core currently calls `refined_advance_receive_until` before invoking `open_frame`; each admitted future step immediately replaces the live receive chain, appends concrete material, and updates logical control. `open_frame` subsequently checks the CTX commitment and ChaCha20-Poly1305 authentication, but callback `None` returns without undoing the already published advance. See [`src/ratchet.rs`](../../beaconcrypt/src/ratchet.rs), especially `decrypt_message_with_ratchet` and `open_frame`, and [`crates/protocol-core/src/ratchet.rs`](../../beaconcrypt-core/src/ratchet.rs), especially `refined_advance_receive_until` and `refined_open_and_finish`.

Moving only the CTX commitment check before publication would not satisfy the objective. The outer value commits to `K || N || A || T || seq || kid`, not directly to the ciphertext body `C`; an attacker can alter `C` while retaining `T` and the outer commitment, pass commitment validation, and then fail AEAD authentication. The transaction boundary MUST therefore include the complete commitment-plus-AEAD open operation.

The current persistent wrapper compounds the behavior by passing every receive call through the unconditional `PersistentServer::commit` helper. It serializes and CASes a successor generation even when the public result is `None`. The receive path requires a distinct state-effect contract; changing generic `commit` to assume that every `None` is unchanged would be incorrect because registration and send operations can consume replay state or key material before returning `None`.

## Required invariants

- Every empty, unparsable, truncated, wrong-sender, too-short, inadmissible, missing-key, commitment-invalid, AEAD-invalid, and replayed frame MUST return rejection with the exact entry state.
- Receive preparation MAY derive bounded candidate material, but it MUST NOT mutate live control, chains, or slots and MUST NOT expose a pending transaction or raw material outside the combined core operation.
- The open callback MUST run at most once and only with the exact core-selected material, sequence, and caller-supplied frame context.
- Callback `None` MUST drop the complete pending transaction and return the original state. It MUST NOT cache the target or any skipped material.
- Callback `Some(plaintext)` MUST lead to one infallible publication step after all structural checks, and the returned state MUST contain the skipped entries but not the consumed target.
- No reported failure branch may occur after the first live-state mutation. Panics, process crashes, allocator aborts, primitive side effects, and physical erasure remain outside the normal-return atomicity claim and MUST be documented separately.
- Operational ratchets and pending transactions MUST remain non-`Clone`, non-`Copy`, and non-serializable as live capabilities.
- Rejected persistent receives MUST perform no snapshot encoding, digest computation, generation increment, or `SnapshotStore::compare_and_swap` call.
- Successful persistent receives MUST preserve the existing result-withholding rule: no plaintext or receive update escapes until the successor snapshot is durably accepted.
- Wire formats, KDF inputs and output partitioning, CTX construction, associated data, public method signatures, and snapshot version 2 MUST remain unchanged.

## Non-goals

- Do not change send semantics. A send attempt continues to consume its allocated key according to the existing one-use policy even if frame construction fails.
- Do not change registration consumption semantics. Accepted registration identifiers and staged response state retain their existing commit rules even when a later operation returns `None`.
- Do not add ratchet mutation as a replay or denial-of-service defense for invalid frames.
- Do not add a public rollback, clone, preview, pending-receive, raw-key, or independently supplied authentication-Boolean API.
- Do not reduce `RATCHET_MAX_GAP` or the serialized receive-cache capacity.
- Do not claim that F* proves concrete HKDF, BLAKE2b, ChaCha20-Poly1305, callback fidelity, serialization, trusted-store behavior, crash durability, compiler erasure, or rate limiting.

## Target receive transaction

The complete receive operation MUST have the following ordering:

```text
parse frame and select peer
        |
plan and preflight target against live state
        |
derive private pending delta without changing live state
        |
run commitment check and AEAD open with pending/cached target material
        |                              |
        | None                         | Some(plaintext)
        v                              v
drop and zeroize pending delta         publish successful state atomically
return rejection                      return plaintext
```

| Phase or outcome | KDF/open work | Volatile state | Persistent state |
| --- | --- | --- | --- |
| Parse, sender, length, admission, capacity, or lookup rejection | No KDF and no open callback | Unchanged | No snapshot or CAS |
| Commitment or AEAD rejection for a cached target | One open callback, no KDF | Unchanged | No snapshot or CAS |
| Commitment or AEAD rejection for a future target | Up to 50 KDF steps and one open callback | Unchanged after pending values are dropped | No snapshot or CAS |
| Successful cached target | One open callback, no KDF | Target swap-removed exactly once | One successor snapshot and CAS |
| Successful future target | Bounded KDF steps and one open callback | Final chain/counter published, skipped keys cached, target consumed | One successor snapshot and CAS |

## Protocol-core data model

Introduce a kernel-private preparation type. Exact field names may change during extraction work, but its ownership and information boundaries MUST follow this shape:

```rust
enum PreparedReceive<ReceiveChain, Material> {
	Cached(PreparedCachedReceive),
	Future(PendingReceive<ReceiveChain, Material>),
}

struct PreparedCachedReceive {
	sequence: u64,
	target_slot: u8,
	last_slot: u8,
	committed_control: RatchetState,
}

struct PendingReceive<ReceiveChain, Material> {
	committed_control: RatchetState,
	final_receive_chain: ReceiveChain,
	staged_slots: [Option<CachedReceiveKey<Material>>; RECEIVE_CACHE_CAPACITY],
	target_sequence: u64,
	target_material: Material,
	first_slot: u8,
	skipped: u8,
}
```

These types MUST be private to `ratchet.rs`, MUST NOT implement `Clone`, and MUST NOT cross the public concrete-kernel boundary. The fixed array and bounded recursive helpers should follow the extraction-compatible style already used for the live cache. Do not introduce `Vec`, iterator-dependent movement, `MaybeUninit`, unsafe code, or a `Clone` bound solely to stage a receive.

The isolated core remains `no_std`. Initialize the staged array with the existing extraction-compatible literal of 50 `None` values because the pinned hax frontend does not support `array::from_fn` or an inline-const repeat for non-`Copy` material. Use `u8`-bounded recursion with explicit `hax_lib::decreases`, move validated entries with `Option::take`, and do not introduce `mem::replace` into the extracted surface. Add the new types and helpers to `HAX_ITEMS` so generated names remain stable, then update the reviewed Option-operation and inventory counts rather than bypassing them.

`PendingReceive` is a delta, not a second complete ratchet. `committed_control` is the state after derivation and logical target removal, `final_receive_chain` is the chain after deriving the target, `staged_slots` contains only the skipped keys at their absolute live destination indices, and `target_material` is kept separate so it can never be transiently published. The live send chain, live receive chain, existing cached material, and logical state remain in place until success. `RatchetChain`, `RatchetMaterial`, its key and nonce components, and intermediate pending entries already receive best-effort erasure through `ZeroizeOnDrop`; dropping a rejected pending transaction MUST transitively drop these values. The implementation MUST review generated temporaries and production key/nonce conversions without claiming physical erasure.

## Preparation algorithm

Retain `plan_receive_until` as the pure admission decision. Preparation MUST first obtain the target and derivation count, enforce the gap and total outstanding-key bounds, and preflight every destination that a successful future receive would need. No KDF or open callback runs for a rejected plan.

For a target at or behind the current receive counter, preparation performs zero derivations. It MUST locate the existing sequence-tagged material, preflight both the target and old-last entries required by swap-removal, and compute the successful logical removal before invoking the open callback. A consumed, zero, or otherwise missing target returns rejection immediately and unchanged.

For a future target, preparation MUST derive exactly `target - receive_sequence` steps without assigning to the live `RefinedRatchet`. The first step borrows the live receive chain; later steps borrow the preceding pending chain. Each intermediate result is sealed to its logical sequence at its absolute destination in `staged_slots`, while the final result is stored as `target_sequence` plus `target_material`. On the final logical advance, preparation MUST apply `finish_receive_with_removal(..., true)`, require that the target slot and last slot are both the just-appended slot, and store the returned post-consumption state as `committed_control`. Every validation failure occurs before live mutation and only drops local pending values.

The preparation helper may reuse the existing pure `advance_receive` and `finish_receive_with_removal` transitions. It MUST NOT reuse the current mutating `refined_execute_receive_steps` on the live state. If compatibility tests still require low-level advancement or `ReceiveDisposition::Retained`, those helpers may remain crate-private or test-only, but the production `concrete_open_and_finish` path MUST no longer publish them on callback failure.

## Open and publication algorithm

Keep the production-facing callback shape `fn(&Material, u64, &Context) -> Option<Plaintext>`. The core MUST select the target material from the existing tagged slot or the separate pending `target_material`, pass the matching `target_sequence`, end the immutable borrow after the callback, and branch on its result.

On `None`, return immediately. A cached preparation contains only copyable metadata and changes nothing; a future preparation drops its final chain, every staged skipped entry, and the separate target material. The live state is therefore identical without reverse-ratcheting, restoring serialized bytes, or cloning secrets.

On `Some(plaintext)`, publication MUST have no reported failure path. For a cached target, apply the already validated target/last whole-entry swap-removal and publish `committed_control`. For a future target, move exactly `staged_slots[first_slot..first_slot + skipped]` into the preflighted live slots, replace the live receive chain with `final_receive_chain`, and assign `committed_control` last. The target material remains in the pending value and MUST be dropped rather than inserted into the live cache. Because a future target is the final appended entry, successful future publication does not need a target/last swap.

Before moving the first value, a private validator MUST establish that every required absolute staged slot is present with its expected sequence, every corresponding live destination is still empty, `target_sequence` is the requested sequence, and `committed_control` has the expected counter and cache without that target. The subsequent bounded movement helper MUST be total under that private invariant and use `Option::take` only across the validated range. This retains the existing design rule that a normal error cannot publish a prefix.

`refined_open_and_finish` and `concrete_open_and_finish` may retain their external signatures, minimizing adapter churn. Their documentation MUST change from “callback failure retains the admitted state” to “callback failure preserves the entry state.” The concrete wrapper MUST continue selecting the lifetime-bound KDF executor internally.

For callback `Some`, the resulting logical and concrete state MUST be identical to the current successful implementation: the same ordered KDF requests, target callback arguments, final receive chain/counter, skipped-key slots, target consumption, and untouched send direction. Only callback `None` changes. A retry after rejection rederives the pending path instead of performing the current zero-step lookup of a retained target.

## Production adapter changes

`open_frame` should remain the single callback that performs the CTX comparison followed by ChaCha20-Poly1305 open. Splitting commitment and AEAD callbacks is unnecessary once the entire callback runs before publication and would expand the trusted classification boundary. Any failure in commitment construction, constant-time comparison, key/nonce conversion, or AEAD open returns `None` and therefore drops the pending delta.

`decrypt_message_with_ratchet` retains its public behavior and frame gates, but its comment and tests MUST state the new all-rejection neutrality contract. `Server::decrypt_message` and `Beacon::decrypt_message` continue selecting exactly one established ratchet and associated-data value before calling it. Rejection MUST not alter the selected peer or any unrelated peer.

The structured receive-update APIs require special care because they currently contain fallible serialization after decryption. Keep a crate-private fallible `RatchetSnapshot::try_capture` and fallible JSON renderer, but make raw `Server` wrappers call them with explicit invariant `expect` messages instead of mapping a post-success error to public `None`. Under reachable core invariants these projections are structurally total; a panic remains outside the normal-return theorem. Persistent wrappers call the fallible forms after durable acceptance and use the separate recoverable-error rule below. It is not acceptable for a normal `None` to follow receive-state mutation.

## Receive effect and persistence wrapper

Add an internal result that makes the mutation effect explicit rather than teaching generic persistence code to interpret arbitrary `Option` values:

```rust
pub(crate) enum ReceiveTransition<T> {
	Rejected,
	Accepted(T),
}
```

The internal server receive entry point returns `Rejected` only under the proven exact-state contract and `Accepted(Decrypted)` only after target consumption. The existing public volatile APIs map this enum back to their unchanged `Option` signatures. Add a mapping helper so `decrypt_and_update` and `decrypt_and_update_json` construct their outputs without invoking decryption twice.

Add a receive-specific persistence helper rather than weakening the existing `commit` contract:

```rust
fn commit_receive<T>(
	&mut self,
	operation: impl FnOnce(&mut Server) -> ReceiveTransition<T>,
) -> Result<ReceiveTransition<T>, PersistenceError>
```

`commit_receive` MUST reject an already poisoned owner before running the operation and MUST set `poisoned = true` before entering code that could panic. If the operation returns `Rejected`, it MUST restore `poisoned = false` and return `Ok(ReceiveTransition::Rejected)` without calculating the next generation, encoding a snapshot, hashing it, loading the store, or calling CAS. The public wrapper then projects this to `Ok(None)`. This also means an unchanged rejection remains available when the current head generation is `u64::MAX`; generation exhaustion matters only when a new state must be committed.

If the operation returns `Accepted(output)`, `commit_receive` MUST use the current successor-snapshot path unchanged: checked generation increment, canonical encoding, successor-head calculation, full-head CAS, local-head replacement, clearing poison, and only then `Ok(ReceiveTransition::Accepted(output))`. The public wrapper then projects this to `Ok(Some(output))`. Any generation, encoding, digest, or CAS error leaves the local owner poisoned and withholds the output. A CAS loser may contain a locally advanced in-memory server, but poisoning prevents that fork from executing or releasing plaintext, while the trusted store remains authoritative.

Because rejection creates no envelope node, the next accepted operation uses the last genuinely committed digest as its `parent_digest` and advances generation from `n` to `n + 1` without a rejection-created gap. `PersistentServer::restore` remains the intentional exception: activation advances the generation even though the decoded protocol payload is unchanged, because that CAS fences competing restorers before either becomes operational.

Only `PersistentServer::{decrypt_message,decrypt_and_update,decrypt_and_update_json}` use `commit_receive`. All three MUST first commit the same authoritative `ReceiveTransition<Decrypted>` produced by `Server`; they MUST NOT decrypt twice or commit a rendered update independently. `decrypt_message` projects the durably accepted `Decrypted` directly. After an accepted durable commit, `decrypt_and_update` captures the now-committed peer state, and `decrypt_and_update_json` serializes that update without another CAS. Add `PersistenceError::OutputEncoding` for a post-commit update/snapshot rendering failure; this error is explicitly not a frame rejection, the target remains durably consumed, and the wrapper remains unpoisoned and usable. Sends, registrations, and response construction continue using unconditional `commit`, because their `None` results do not imply unchanged state. Keep the existing regression that a generic operation may return `None` after mutation.

Skipping CAS on rejection delays stale-owner discovery but does not create a state fork: the stale owner releases no plaintext and changes no state. Its next accepted receive or other state-changing operation attempts the existing CAS, loses, withholds output, and becomes poisoned. If a deployment requires eager liveness detection for rejected traffic, add a separate read-only trusted-head check to `SnapshotStore`; do not manufacture a successor generation and call it state-neutral.

The binding-backed in-memory store inherits the same rule. A rejected C, Go, or Python server receive leaves exported checkpoint bytes bit-for-bit unchanged. Public binding signatures and ownership rules do not change.

## Crash and panic behavior

- A KDF or open callback panic during preparation/open leaves the live ratchet unchanged because publication has not started. A `PersistentServer` remains poisoned because its receive helper set the flag before calling the operation.
- A process crash before a successful persistent CAS leaves the trusted snapshot authoritative at the old state and releases no plaintext through the API. Restart may process the frame again.
- A process crash after the store accepts the successor but before the caller receives plaintext can lose delivery while retaining consumption. This existing availability limitation is not rollback and remains outside the atomic result-delivery claim.
- A post-commit `OutputEncoding` error leaves the accepted receive durably consumed and the wrapper unpoisoned. It is an output-construction failure, not a rejected frame, and retry of the same frame is a neutral replay rejection.
- An impossible private-invariant branch during publication is a bug, not a frame rejection. All such checks MUST occur before mutation, and the proof and tests MUST establish that the movement phase cannot report failure.
- Raw `Server` and `Beacon` remain volatile single-owner types and make no crash-durability claim.

## Persistence and wire compatibility

No Cap'n Proto schema, ciphertext layout, sequence encoding, associated-data construction, JSON field, snapshot envelope, snapshot version, or trusted-head algorithm changes.

Version-2 snapshots produced by the old behavior may contain a target key retained after a failed receive and may contain all 50 active cache entries. Restoration MUST continue accepting structurally valid legacy snapshots. An invalid retry against such a cached key is neutral; a valid retry consumes it. A full legacy cache continues rejecting new future targets until a cached authentic frame is successfully consumed. Do not reduce the capacity to the newly reachable steady-state maximum.

Do not strengthen the general restored/reachable invariant to claim that every cached entry was skipped by a successful receive or that cache length is at most 49. Those properties describe fresh executions of the new high-level lifecycle, not the complete set of version-2 states accepted from trusted canonical history. Upgrading also does not erase target material already retained in an old authoritative snapshot.

From a fresh state under the new production lifecycle, a successful future receive derives through the target and then consumes it, so it retains at most the skipped entries. A distance-50 success from an empty cache therefore ends with 49 cached keys rather than 50. The admission preflight still uses capacity 50 because the private candidate temporarily contains the target and because legacy restored states remain supported.

## Rust test plan

### Protocol-core unit tests

- Add generic-state tests proving that callback `None` at the next sequence, a multi-step future sequence, and the gap boundary preserves control, both chains, slot length/order, every tagged material value, and callback output state exactly.
- Count synthetic KDF invocations to show that a rejected future target derives exactly the planned number of temporary steps and that retry rederives them without changing live state.
- Test successful future publication at distances 1 and 50: the counter and final chain reach the target, all and only skipped materials remain, the target is absent, and replay is neutral.
- Test cached-target rejection with a non-last target and assert that no swap occurs; then accept the same target and assert exact whole-entry swap-removal.
- Test plan rejection, capacity rejection, missing old targets, zero, and `u64::MAX` without invoking the open callback or KDF executor beyond the stated admission rules.
- Add a test-only complete snapshot helper that copies observable bytes for comparison; do not add `Clone`, `Eq`, or public secret access to production kernel types.

### Production and integration tests

- Change `tests/protocol.rs` so every bit mutation in ciphertext body, AEAD tag, and commitment is rejected with an exact before/after receive-state comparison, then confirm that the authentic frame still opens.
- Cover both server-to-beacon and beacon-to-server paths through the existing test-only endpoint abstraction.
- Replace tests that expect corrupted commitments or AEAD bodies to fill the receive cache. Repeated invalid frames at sequences 1 through 50, including the boundary, MUST leave the initial state unchanged.
- Rewrite test-only fixtures that use `RatchetManager::ratchet_recv_until`, because that helper currently advances by deliberately returning callback failure and will become neutral. Prefer constructing state through successful receive operations or generic core fixtures; if an imperative advancement hook is unavoidable, keep it narrowly test/dev-feature gated and outside the production concrete lifecycle.
- Preserve receive-window coverage using successful out-of-order frames: accepting the boundary caches the skipped keys and consumes the boundary target, delayed authentic frames consume those cached keys, and replay is neutral.
- Strengthen malformed, truncated, wrong-sender, short-payload, sequence-relabel, missing-commitment, swapped-tag/commitment, over-gap, capacity, and replay tests to compare the complete state rather than only the public counter.
- Retain valid known-answer, commitment-binding, multi-opening negative-control, registration, and round-trip tests because the cryptographic transcript and accepted-frame behavior do not change.

### Persistence tests

- Replace `failed_future_receive_advancement_is_committed_and_restored` with a test that captures the head, snapshot bytes, CAS count, poison flag, and complete peer-ratchet state, rejects a future frame corrupted in the ciphertext body, and asserts every captured value is unchanged.
- Repeat the persistence neutrality test for malformed input, commitment corruption, tag corruption, wrong sender, over-gap sequence, and replay through `decrypt_message`, `decrypt_and_update`, and `decrypt_and_update_json`.
- After each rejected case, deliver the authentic frame and assert exactly one generation increment and one CAS before plaintext or update output is returned.
- Inject post-commit update and JSON rendering failures, assert `PersistenceError::OutputEncoding`, verify that the successful receive remains durably committed, and verify that the wrapper is not poisoned and replay is neutral.
- Add a stale-owner test in which an owner first rejects a frame without CAS or poisoning, then attempts an accepted frame after another owner advances the store; the stale owner MUST lose CAS, withhold plaintext, and become poisoned.
- Arm the test store's forced next-CAS failure, reject a frame, and prove that rejection neither invokes nor consumes the failure; the following authentic receive MUST hit that failure, withhold plaintext, and poison the owner.
- Preserve CAS-failure, generation-exhaustion, panicking-operation, restoration-activation, registration-consumption, send-consumption, and “changed state despite `None`” tests for non-receive paths.
- Restore an old-format-valid snapshot with a full 50-entry receive cache and verify compatibility, neutral invalid retry, successful cached consumption, and later forward progress.
- For binding stores, assert that export bytes are identical before and after rejection and change only after a successful state-changing receive.

## F* proof migration

The generated ratchet module and handwritten `Beaconcrypt_protocol_core.Ratchet.Lemmas.fst` MUST move the production proof surface from failure retention to preparation neutrality and success-only publication. Low-level pure facts about `finish_receive(..., false)` may remain if still used, but they MUST NOT be presented as the high-level production receive behavior.

The caller-usable capstone MUST have this shape over full refined-state equality:

```text
let final_state, result = open(entry_state, frame) in

valid_refined(final_state)
and (result = None implies final_state = entry_state)
and (result = Some(plaintext) implies successful_receive(entry_state, final_state, target, plaintext))
```

Define a proof-visible `valid_pending(entry, pending, target)` relation. It MUST connect the admitted nonzero derivation count to the unchanged `cached + derivations <= 50` rule, identify `pending.final_receive_chain` as the exact canonical chain after those derivations, identify every absolute staged slot as the canonical skipped sequence/material pair, identify the separate target as the canonical requested material, state that the target is absent from live and staged slots, characterize `committed_control` as post-target consumption, and preserve every entry-state field and old association during preparation.

Add or replace lemmas establishing:

- rejected admission returns the original complete refined state and invokes neither the KDF executor nor open callback;
- valid preparation derives the exact bounded sequence/slot/material trace while leaving the live refined state equal to its input;
- the pending target material is exactly the canonical `material_at` value for the requested sequence under the fixed starting chain and executor;
- callback `None` returns the original complete refined state for both cached and future preparations;
- callback `Some` on a cached target performs the exact prevalidated whole-entry removal;
- callback `Some` on a future target publishes the exact final chain and counter, preserves all old associations, appends exactly the skipped canonical entries, excludes the target, and returns the callback plaintext;
- successful publication and all rejection branches preserve `valid_refined`, generic reachability, concrete reachability, and the paired beacon/server directional-session predicate;
- replay is neutral after success, and a later authentic retry after any number of rejected attempts follows the same state transition as receiving it without those attempts; and
- rejected frames cannot consume cache capacity, while a successful maximum-gap receive ends with the exact skipped-key count.

Replace the current theorem and inventory language that callback `None` retains the admitted state. The new theorem should state full input-state equality, including control, send chain, receive chain, and every material slot. Proofs should distinguish KDF callback execution from live-state mutation: admitted invalid future frames may invoke the pure executor up to the bound even though the returned state is identical.

Specifically replace `admitted_receive_failure_retains_advanced_state`, `failed_receive_fills_cache_and_rejects_next_future`, and `refined_open_none_retains_selected_material`; update `refined_open_some_consumes_selected_material`, `refined_open_and_finish_preserves_validity`, and the generic/concrete reachability theorems around the new pending relation. Reframe `failed_receive_retry_consumes_once` as an already-cached or restored-key fact rather than a public failed-future trace. Low-level neutral completion and exact swap-removal lemmas may remain, and `successful_receive_releases_capacity_for_next_future` remains relevant to restored legacy full-cache states.

Regenerate the extracted F* module, review the diff rather than silently accepting it, update the strict handwritten lemmas without `assume`, `admit`, or `--lax`, and add the required plain-English explanation to [`doc/formal-verification-analysis.md`](../formal-verification-analysis.md).

## ProVerif model migration

The existing failed-receive suite intentionally models and checks a 50-entry cache produced by rejected frames. That scenario becomes false and MUST NOT be retained by merely changing prose. Replace it with a state-neutral rejected-receive scenario whose rejection branch continues with the exact pre-attempt symbolic receiver state, followed by a reachable authentic future delivery, skipped-key retention from that success, replay rejection, and delayed cached deliveries.

Remove or rewrite the explicit `ready -> retained -> full-cache -> consumed -> refilled` terms and events in `proofs/pro-verif/environment.pvl`. The replacement MUST include reachability witnesses so rejection neutrality, later success, replay rejection, and delayed delivery cannot pass vacuously. It should continue composing an independently rooted honest receive state with replicated attacker-owned registration if that isolation question remains in scope.

Use one exact bounded replacement schedule to keep the symbolic model reviewable. After sequence 1 is consumed, reject a forged future sequence-3 frame and a repeat while carrying the exact same ready-state term; then accept the honest sequence-3 frame, publish only skipped sequence 2, consume sequence 3, and reject replay relative to the exact post-success state. In a separate capacity leg, successfully receive sequence 51 from counter 1 so 49 skipped keys remain, reject a distance-two future receive because `49 + 2 > 50`, consume one cached key, and then accept that future distance. Every rejection and success event MUST have a non-vacuity witness.

Replace rather than drop the failed-receive compromise scenario. Disclosure immediately after rejection MUST expose the same symbolic state term as disclosure immediately before rejection, and the model MUST remove any claim that rejection added skipped or target cached material. Revealing the unchanged live chain can still expose future material in the ideal compromise model, so the intended result is “rejection did not enlarge state or exposure,” not “future secrets survive live-chain compromise.” Update the expected query counts and classifications in `check-results.awk` to match the reviewed replacement.

Update `crates/protocol-core/Makefile`, `crates/protocol-core/README.md`, `proofs/trusted-boundary.md`, and `proofs/check-inventory.sh` for the replacement files, events, processes, queries, and structural guards. Remove the exact 50-entry failed-cache assertions and replace them with guards that require the rejection-neutral state reuse and the successful skipped-key trace. Add `tests/server.rs` to the validation inventory because durable receive neutrality is now part of the reviewed security boundary. Refresh only the reviewed hashes in `proofs/reviewed-inventory.txt` after the complete proof and model changes are understood.

## Maintained documentation updates

- Update [`doc/protocol.md`](../protocol.md) so receive steps are described as private preparation followed by success-only publication; remove instructions to retain advanced state on authentication failure.
- Update [`doc/formal-verification.md`](../formal-verification.md) and [`doc/formal-verification-analysis.md`](../formal-verification-analysis.md) to replace failed-admission retention, cache-fill, retry-without-KDF, and retained-state compromise claims with the proved state-neutral behavior and repeated-work caveat.
- Update [`doc/persistence.md`](../persistence.md) to state that rejected receives neither advance the snapshot head nor call CAS, while accepted receives and every other state-changing operation retain durable result withholding and stale-owner fencing.
- Update the root README and binding-facing persistence comments so callers save a new checkpoint after accepted/state-changing operations, while a normal rejected receive leaves the exported checkpoint unchanged.
- Update [`crates/protocol-core/proofs/trusted-boundary.md`](../../beaconcrypt-core/proofs/trusted-boundary.md) so the adapter and proof inventory distinguishes pure candidate derivation from live publication and accurately records callback, persistence, and crash assumptions.
- Leave prior documents in `doc/impl/` as historical records. This plan supersedes their descriptions of failed receive retention; do not silently rewrite the behavior they recorded at their original stages.

## Security and performance consequences

State neutrality removes the ability of unauthenticated traffic to consume receive-cache capacity or move the persistent ratchet head. It also removes the zero-KDF retry optimization for invalid future frames. The same rejected boundary frame can force up to 50 HKDF steps every time it is submitted, so deployments MUST treat per-peer rate limiting, admission quotas, and transport-level replay filtering as availability controls. Such controls are outside the cryptographic state machine and MUST NOT alter the ratchet in response to rejection.

Preparation temporarily retains up to 50 derived materials plus one final chain. This is bounded by the existing cache constant. The implementation should avoid heap allocation in the extracted core, review stack impact on supported targets, and benchmark accepted and rejected distance-1 and distance-50 receives. A successful future frame performs one derivation pass, not a validation pass followed by a second commit pass.

The change improves normal-return rollback semantics but does not make callback code transactional. KDF, hash, comparison, and AEAD callbacks remain trusted to be deterministic/pure where required by the formal model, and their timing, logs, hardware side effects, panics, and retained external copies remain outside the state-equality theorem.

## Implementation order

1. Add focused failing core and integration tests for complete rejection neutrality without changing production behavior.
2. Introduce private cached/future preparation types and extraction-compatible bounded derivation helpers in `protocol-core`.
3. Change generic and concrete open lifecycles to publish only callback success, then update production adapter comments and tests.
4. Add `ReceiveTransition`, route volatile receive/update methods through it, and eliminate normal `None` results after successful publication.
5. Add `PersistentServer::commit_receive`, migrate all three persistent receive entry points, and add head/store/CAS neutrality and stale-owner tests.
6. Preserve snapshot version 2 restoration, add legacy full-cache coverage, and verify binding exports remain unchanged on rejection.
7. Regenerate extraction, replace F* retention lemmas with preparation-neutrality and success-publication lemmas, and verify concrete/session reachability.
8. Replace the ProVerif failed-receive/cache-fill scenarios and update result controls, structural inventory checks, and reviewed hashes.
9. Update maintained protocol, persistence, verification, analysis, README, and trusted-boundary documentation.
10. Run the complete validation matrix and review all generated, proof, persistence, and public-behavior diffs.

## Acceptance criteria

- Every normal `None` from a volatile receive API leaves the complete live state equal to its entry state.
- Every `Ok(None)` from a persistent receive API leaves the complete live server, `SnapshotHead`, trusted snapshot bytes, generation, CAS count, and poison flag equal to their entry values.
- Every successful volatile receive advances through the selected sequence, caches exactly the skipped keys, consumes the target, and rejects replay.
- Every successful persistent receive performs exactly one successor CAS and withholds its output until that CAS succeeds.
- A post-commit update-rendering failure is returned as `PersistenceError::OutputEncoding`, never `Ok(None)`, and does not roll back or poison the durably accepted receive.
- No send or registration consumption behavior changes.
- Existing version-2 snapshots, including structurally valid full receive caches, restore without a format migration.
- No operational or pending ratchet type becomes clonable, serializable as a live capability, or publicly constructible.
- The generated F* diff, strict lemmas, ProVerif models, expected result classifications, trust-boundary inventory, and plain-English analysis all describe the same success-only publication semantics.
- All Rust feature combinations, bindings, tests, formatting, linting, generated-artifact checks, and locked proof verification pass.

## Required validation

Run and record:

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test
cargo check --no-default-features --features pqxdh,beacon --lib
cargo check --no-default-features --features pqxdh,server --lib
make -C crates/protocol-core verify
make -C crates/protocol-core check-inventory
cargo build --release --features gobinds
go test -race ./...
uv run maturin develop --uv
uv run pytest tests
```

During proof development, run the focused protocol-core, protocol integration, server persistence, and ProVerif targets before the complete matrix. Review generated F* and ProVerif diffs manually; do not edit extracted F* or blindly refresh the reviewed inventory hashes. Run `check-generated` only with the intended generated baseline present so it detects extraction drift rather than masking it.
