# PR #2 Completion Guide: Finish the Verified Receive-Slot Refactor

**Repository:** `0xd6cb6d73/beaconcrypt`
**PR:** `#2` — `Align concrete receive-key storage with verified core fixed slots and mirror swap-removal`
**Reviewed PR head:** `152c5476eda4345615afcd9fed2be806971ac9ec`
**Base:** `proof`
**Purpose of this guide:** finish PR #2 so it implements the intended mechanized receive-slot refinement, without undoing the useful fixed-array work already present or changing unrelated protocol behavior.

> Historical scope notice: this guide records the constraints of the receive-slot-only PR #2 work. Its parallel production receive array, returned-slot/removal-plan boundary, send-key staging, and former six-field `RatchetManager` schema were superseded by the extracted `RefinedRatchet` follow-up. The current kernel owns typed chains and fixed concrete-material slots, production supplies only the opaque HKDF step, and persistence uses the five fields documented in [persistence.md](persistence.md) and [formal-verification-stage-3.md](formal-verification-stage-3.md).

---

## 1. Goal

PR #2 completed the first structural step: the production receive-key cache became a fixed 50-slot array parallel to the verified logical receive cache. Its remaining goal was to move the **sequence-to-slot lookup**, **swap-removal plan**, and **restoration slot assignment** into `protocol-core`, extract those decisions through hax, prove them in F\*, and make production consume those verified decisions directly.

PR #2's target architecture was:

```text
                     protocol-core / F*

sequence ───────► lookup_receive_key ───────► physical slot
                                                   │
advance_receive ───────────────────────────────► append slot
                                                   │
finish_receive_with_removal ────────────────► target/last slots
                                                   │
restore_receive_key_with_slot ──────────────► restore slot
                                                   │
                                                   ▼
                     production recv_slots array
                     [Option<KeyMaterial>; 50]
```

Production remains responsible for opaque cryptographic work: one concrete HKDF ratchet step per successful logical advancement, storing/moving/dropping `KeyMaterial`, serde mechanics, and the surrounding high-level receive trace. It must no longer independently decide which logical sequence corresponds to which physical receive slot.

The current follow-up goes further: `RefinedRatchet<SendChain, RecvChain, KeyMaterial>` owns logical control, both opaque typed chains, and `[Option<KeyMaterial>; 50]` in the extracted kernel. Production compiles and calls this same kernel with HKDF as the sole opaque step callback; lookup returns paired material, successful finish performs swap-removal internally, and refined restoration accepts `(sequence, material)` atomically.

---

## 2. Current PR state to preserve

The following work in PR #2 is directionally correct and should be retained.

### 2.1 Fixed concrete receive array

The production receive cache is now:

```rust
type ReceiveKeySlots = [Option<KeyMaterial>; verified_ratchet::RECEIVE_CACHE_CAPACITY];

recv_slots: ReceiveKeySlots
```

instead of:

```rust
HashMap<u64, KeyMaterial>
```

Keep the fixed-capacity array representation.

Use `empty_receive_key_slots()` for construction, initialization, reset, and persistence restoration. The `recv_slots` name distinguishes the private physical array from the externally persisted `recv_past` sequence map.

### 2.2 Allocation into `ReceiveAdvance::slot`

PR #2 correctly stores the concrete result of one receive-chain ratchet step in the physical slot returned by:

```rust
verified_ratchet::advance_receive(self.control)
```

Keep this model. Do not return to sequence-keyed insertion.

### 2.3 Packed concrete representation

PR #2 keeps active concrete keys packed in the prefix of the array and mirrors the current core swap-removal layout. Keep the packed-array invariant:

```text
for n = control.receive_cache_len():

slot < n   => recv_slots[slot].is_some()
slot >= n  => recv_slots[slot].is_none()
```

The missing work is to make the slot decisions themselves verified, not to replace this representation.

### 2.4 Persistence schema compatibility

PR #2 preserves the existing external six-field `RatchetManager` serde representation and continues serializing `recv_past` as a sequence-to-`KeyMaterial` map.

Keep this behavior. Physical slot numbers are an in-memory representation detail and must not become persisted identity.

### 2.5 Existing public sequence-number APIs

Keep the public/current sequence-facing APIs. Do not require callers to carry physical slots or long-lived slot-bearing receive capabilities.

Physical receive slots can move after successful swap-removal. Sequence numbers remain the stable external identity.

---

# 3. Missing elements that must be implemented

The work below is required before PR #2 should be considered an implementation of the mechanized refinement plan.

---

## 3.1 Add verified sequence-to-slot lookup to `protocol-core`

### File

```text
crates/protocol-core/src/ratchet.rs
```

### Required API

Add an extracted pure function equivalent to:

```rust
pub fn lookup_receive_key(
    state: RatchetState,
    sequence: u64,
) -> Option<u8> {
    let mut slot = 0_u8;

    while (slot as usize) < RECEIVE_CACHE_CAPACITY {
        if slot >= state.receive_cache.len {
            return None;
        }

        if state.receive_cache.entries[slot as usize] == sequence {
            return Some(slot);
        }

        slot += 1;
    }

    None
}
```

The exact loop form may be changed if the pinned hax version does not extract it cleanly. If necessary, use a fuel-bounded helper whose fuel starts at `RECEIVE_CACHE_CAPACITY` and strictly decreases.

Do **not** solve extraction difficulty by:

- keeping the scan in production;
- making the lookup opaque to hax;
- adding an assumption about the result;
- using an unverified collection helper whose semantics are hidden from F\*.

### Required semantics

For valid states:

```text
lookup_receive_key(state, sequence) == Some(slot)
    iff
slot is the unique active SequenceCache slot containing sequence
```

and:

```text
lookup_receive_key(state, sequence) == None
    iff
sequence is not present in the active logical receive cache
```

The completeness direction is required. Production will use `None` as the authoritative statement that no logical receive capability exists.

### Production consequence

Delete the production helper:

```rust
fn receive_key_slot(&self, sequence: u64) -> Option<u8>
```

and replace all uses with:

```rust
verified_ratchet::lookup_receive_key(self.control, sequence)
```

After this change there must be **no receive sequence-to-slot scan in production code**.

---

## 3.2 Add a verified concrete removal plan

The current core `finish_receive` proves the logical swap-removal but returns only the new state and disposition. PR #2 therefore reconstructs the physical removal operation in `src/shared.rs`. That is the main remaining adapter gap.

### File

```text
crates/protocol-core/src/ratchet.rs
```

### Add types

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveRemoval {
    pub target_slot: u8,
    pub last_slot: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveFinishWithRemoval {
    pub state: RatchetState,
    pub disposition: ReceiveDisposition,
    pub removal: Option<ReceiveRemoval>,
}
```

### Add detailed operation

Move the actual implementation of logical receive completion into:

```rust
pub fn finish_receive_with_removal(
    state: RatchetState,
    target: u64,
    slot: u8,
    authenticated: bool,
) -> ReceiveFinishWithRemoval
```

Required behavior:

```text
wrong/missing (target, slot):
    disposition = Missing
    state = old state
    removal = None

authentication failure:
    disposition = Retained
    state = old state
    removal = None

authentication success:
    disposition = Consumed
    state = logical swap-removal result
    removal = Some {
        target_slot = slot,
        last_slot = old receive_cache_len - 1
    }
```

### Keep the existing API as a wrapper

Do not break current callers or existing proofs unnecessarily. Rewrite existing `finish_receive` as a projection:

```rust
pub fn finish_receive(
    state: RatchetState,
    target: u64,
    slot: u8,
    authenticated: bool,
) -> ReceiveFinish {
    let finished = finish_receive_with_removal(
        state,
        target,
        slot,
        authenticated,
    );

    ReceiveFinish {
        state: finished.state,
        disposition: finished.disposition,
    }
}
```

There must be only **one** implementation of the completion decision. Do not duplicate the logical transition between the old and new functions.

---

## 3.3 Make production apply the verified removal plan

### File

```text
src/shared.rs
```

Replace the current pattern where production computes:

```rust
let last_slot = self.control.receive_cache_len() - 1;
```

and manually infers what the core did.

The production path must instead use:

```rust
let finished = verified_ratchet::finish_receive_with_removal(
    self.control,
    seq,
    slot,
    authenticated,
);
```

On `Consumed`, require `finished.removal == Some(...)` and apply exactly that operation:

```rust
self.recv_slots.swap(target_index, last_index);
let removed = self.recv_slots[last_index].take();
```

Then publish:

```rust
self.control = finished.state;
```

### Required transaction order

For successful authentication:

```text
1. verified lookup identifies current slot
2. detailed verified completion returns new logical state + removal plan
3. validate removal-plan indices against concrete array bounds/occupancy
4. swap concrete target/last slots
5. take/drop the old last concrete key
6. publish finished.state
```

Do not publish the new core state before the concrete move is complete.

### Failure behavior

For `Retained`:

- `removal` must be `None`;
- `finished.state` must equal the current state;
- production must perform no concrete slot mutation.

For `Missing`:

- production must remain state-neutral;
- no concrete slot mutation;
- no concrete KDF step.

---

## 3.4 Add slot-returning verified restoration

PR #2 currently restores the logical cache with the old API and then separately walks the resulting cache to decide where concrete material belongs. The final state is reasonable, but the slot assignment is still an adapter-side reconstruction.

### File

```text
crates/protocol-core/src/ratchet.rs
```

### Add type

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveRestoreStep {
    pub restore: RatchetRestore,
    pub slot: u8,
}
```

### Add operation

```rust
pub fn restore_receive_key_with_slot(
    restore: RatchetRestore,
    sequence: u64,
) -> Option<ReceiveRestoreStep>
```

It must perform the same validation as existing `restore_receive_key`, append the sequence, and return the physical slot produced by that same `SequenceCache::append`.

### Keep compatibility wrapper

Rewrite the old function as:

```rust
pub fn restore_receive_key(
    restore: RatchetRestore,
    sequence: u64,
) -> Option<RatchetRestore> {
    restore_receive_key_with_slot(restore, sequence)
        .map(|step| step.restore)
}
```

As with completion, there must be one implementation of restoration validation/append behavior.

---

## 3.5 Make deserialization consume the verified restoration slot directly

### File

```text
src/deser.rs
```

Keep the external input type:

```rust
recv_past: HashMap<u64, DirectionalKeyMaterial<...>>
```

This temporary serde map is part of persistence parsing and is not the production receive cache.

Change the restoration flow from:

```text
restore all logical sequences
finish_restore
walk resulting control cache
look each sequence up in temporary map
place material into corresponding array slot
```

to:

```text
sort persisted (sequence, material) pairs
start_restore
for each pair:
    restore_receive_key_with_slot
    place material directly into step.slot
    restore = step.restore
finish_restore
```

Use a structure equivalent to:

```rust
let mut entries = data.recv_past.into_iter().collect::<Vec<_>>();
entries.sort_unstable_by_key(|(sequence, _)| *sequence);

let mut recv_slots = empty_receive_key_slots();
let mut restore = verified_ratchet::start_restore(data.send_ctr, data.recv_ctr);

for (sequence, directed) in entries {
    let step = verified_ratchet::restore_receive_key_with_slot(
        restore,
        sequence,
    )
    .ok_or_else(|| D::Error::custom(
        "recv_past exceeds the verified cache capacity or contains an invalid sequence",
    ))?;

    let slot = step.slot as usize;
    if slot >= recv_slots.len() || recv_slots[slot].is_some() {
        return Err(D::Error::custom(
            "verified receive restoration returned an invalid concrete slot",
        ));
    }

    recv_slots[slot] = Some(directed.material);
    restore = step.restore;
}

let control = verified_ratchet::finish_restore(restore);
```

Do not persist or deserialize physical slot numbers.

---

## 3.6 Make serialization fail closed for both directions of divergence

### File

```text
src/ser.rs
```

PR #2 already rejects an active logical slot whose concrete array entry is `None`. Keep that behavior.

Add the missing inverse check: an inactive physical slot must not contain concrete key material.

Before serializing map entries:

```rust
let len = self.control.receive_cache_len() as usize;

if len > self.slots.len() {
    return Err(S::Error::custom(
        "logical receive cache exceeds concrete slot capacity",
    ));
}

if self.slots[len..].iter().any(Option::is_some) {
    return Err(S::Error::custom(
        "inactive receive slot contains concrete key material",
    ));
}
```

Then serialize only active slots `0..len`, mapping each through `control.receive_key_at(slot)`.

Serialization must never silently omit concrete material that violates the positional invariant.

---

## 3.7 Re-export the new core APIs

### File

```text
crates/protocol-core/src/lib.rs
```

Re-export, according to the crate's existing re-export style:

```text
lookup_receive_key
ReceiveRemoval
ReceiveFinishWithRemoval
finish_receive_with_removal
ReceiveRestoreStep
restore_receive_key_with_slot
```

Do not remove existing `finish_receive` or `restore_receive_key` exports.

---

## 3.8 Add the new operations to the hax extraction whitelist

### File

```text
crates/protocol-core/Makefile
```

Extend `HAX_ITEMS` with the new core functions/types needed by F\*:

```make
+beaconcrypt_protocol_core::ratchet::lookup_receive_key \
+beaconcrypt_protocol_core::ratchet::ReceiveRemoval \
+beaconcrypt_protocol_core::ratchet::ReceiveFinishWithRemoval \
+beaconcrypt_protocol_core::ratchet::finish_receive_with_removal \
+beaconcrypt_protocol_core::ratchet::ReceiveRestoreStep \
+beaconcrypt_protocol_core::ratchet::restore_receive_key_with_slot \
```

Keep the existing selectors for `finish_receive` and `restore_receive_key` so wrapper correspondence remains proof-visible.

Do not hand-edit generated F\* extraction to simulate these additions.

---

# 4. Required F\* work

### File

```text
crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst
```

The goal is not merely to make the new functions typecheck. Add explicit lemmas that justify production's use of their returned physical slots.

---

## 4.1 Lookup soundness and completeness

For `valid_state state`, prove the equivalent of:

```text
lookup_receive_key state sequence = Some slot
    => cache_slot state.receive_cache sequence slot
```

and:

```text
lookup_receive_key state sequence = None
    => not cache_has state.receive_cache sequence
```

Also establish completeness, either directly or as the contrapositive of the second theorem:

```text
cache_has state.receive_cache sequence
    => lookup_receive_key state sequence <> None
```

The proof must rely on the existing uniqueness invariant for active logical receive sequences.

---

## 4.2 Detailed completion/wrapper equivalence

Prove for every input that:

```text
finish_receive(...).state
    == finish_receive_with_removal(...).state

finish_receive(...).disposition
    == finish_receive_with_removal(...).disposition
```

This establishes that adding concrete-slot metadata does not change the existing verified logical transition.

---

## 4.3 Missing/retained results produce no removal

Prove:

```text
Missing  => removal == None and state unchanged
Retained => removal == None and state unchanged
```

For a valid matching `(target, slot)` and `authenticated == false`, also retain the existing theorem that the same candidate remains in the same logical slot.

---

## 4.4 Successful removal plan is exact

For valid state and an active matching `(target, slot)`, prove:

```text
finish_receive_with_removal(state, target, slot, true)
    => disposition == Consumed
    => removal == Some r
    => r.target_slot == slot
    => r.last_slot + 1 == old cache length
    => new cache length + 1 == old cache length
```

Prove the physical logical-array shape production mirrors:

```text
if target_slot != last_slot:
    new logical entry[target_slot] == old logical entry[last_slot]

old target is absent
all other logical sequences survive exactly once
```

Existing consumption/preservation lemmas should be reused rather than replaced.

---

## 4.5 Restoration slot shape

For `valid_restore restore`, prove successful restoration returns exactly the append slot:

```text
restore_receive_key_with_slot restore sequence = Some step
    => step.slot == old logical cache length
    => cache_slot step.restore.state.receive_cache sequence step.slot
    => valid_restore step.restore
```

Also prove old/new restoration wrapper equivalence and identical accept/reject behavior.

---

## 4.6 Preserve all existing proofs

Do not remove, weaken, or replace existing F\* results for:

- counter no-wrap/exhaustion;
- receive gap and capacity;
- one-step receive advancement;
- receive-cache validity/uniqueness;
- failed-authentication retention;
- zero-cost retry;
- target consumption;
- preservation of non-target cached keys;
- replay rejection;
- capacity release;
- restoration validity;
- send capabilities;
- peer isolation.

The new work is an extension of the existing proof surface.

---

# 5. Deviations in the current PR and required disposition

This section distinguishes **blocking deviations** from **acceptable deviations**. Do not mechanically rewrite every difference from the earlier plan.

---

## 5.1 Blocking: production still performs sequence-to-slot lookup

### Current PR

`recv_key` and `complete_recv_key` use production `receive_key_slot`, which scans `control.receive_key_at(...)`.

### Required correction

Add and prove `protocol-core::lookup_receive_key`, migrate every production receive lookup to it, and delete `RatchetManager::receive_key_slot`.

### Why blocking

This lookup is one of the decisions the refactor was specifically intended to move into the extracted core. Keeping it in production leaves a material adapter refinement unmechanized.

---

## 5.2 Blocking: production computes the removal plan itself

### Current PR

Production calls old `finish_receive`, then calculates:

```rust
let last_slot = self.control.receive_cache_len() - 1;
```

and manually reproduces the core swap-removal.

### Required correction

Add `finish_receive_with_removal` and consume the returned `ReceiveRemoval` exactly.

### Why blocking

The current code is consistent with today's core implementation but is coupled to its representation through duplicated logic. A future verified core representation change could invalidate the production mirror without changing the old `ReceiveFinish` API.

---

## 5.3 High priority: restoration slot assignment is reconstructed outside core

### Current PR

The old restore API builds `control`; production then reads the final logical slots and matches material back to them.

### Required correction

Use `restore_receive_key_with_slot` and place each concrete material into the slot returned by the same verified append transition.

### Why important

This makes restoration subject to the same direct positional refinement as live receive advancement.

---

## 5.4 Blocking: no new hax/F\* proof surface

### Current PR

No changes to:

```text
crates/protocol-core/src/ratchet.rs
crates/protocol-core/src/lib.rs
crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst
```

and the extraction whitelist does not contain the proposed detailed operations.

### Required correction

Implement Sections 3, 4, and 3.8 of this guide.

### Why blocking

Without this, the PR is a fixed-array adapter refactor, not the mechanized refinement refactor it is intended to become.

---

## 5.5 Medium: serializer ignores concrete keys in inactive slots

### Current PR

Serialization checks that every active logical slot has concrete material, but does not reject `Some(KeyMaterial)` entries after the logical length.

### Required correction

Add the inactive-tail check described in Section 3.6 and a regression test.

---

## 5.6 Medium: some receive tests now assert only logical length

### Current PR

Several former map-length assertions were converted to `control.receive_cache_len()` because the new receive-slot array always has physical length 50.

### Required correction

When the purpose of a test is concrete/logical correspondence, assert concrete occupancy as well:

```rust
assert_eq!(
    ratchet.recv_slots.iter().flatten().count(),
    expected,
);
assert!(ratchet.receive_slots_match_control());
```

Do not use logical length alone as evidence that concrete key storage is correct.

---

## 5.7 Medium: trust-boundary documentation is only partially updated

### Current PR

OR-12 and AR-01 were changed, but the final mechanized design requires updates to at least:

```text
OR-12
OR-14
AR-01
AR-02
AR-04
AR-06
HB-01
```

### Required correction

Update these only after the corresponding implementation/proof work exists.

In particular:

- OR-12 must no longer list `receive_key_slot` once it is deleted;
- OR-12 should state that lookup and removal-plan decisions come from extracted core operations;
- OR-14/AR-06 should mention `restore_receive_key_with_slot`;
- AR-04 should state that successful production removal applies the exact verified target/last plan;
- HB-01 should mention lookup characterization, explicit removal-slot shape, and restoration-slot correspondence.

Do not claim these properties in documentation before they are implemented and checked.

---

## 5.8 Required: distinguish private slots from the persisted map

Use the `ReceiveKeySlots` alias, `empty_receive_key_slots()` constructor, `recv_slots` private field, and `receive_slots_match_control()` invariant helper. The `recv_past` name remains reserved for the compatible external sequence-keyed persistence field.

---

## 5.9 Acceptable: concrete removal uses `take`/assignment rather than `swap` today

PR #2 currently does:

```rust
let removed = recv_slots[target].take();
recv_slots[target] = recv_slots[last].take();
```

For the current packed layout, this is extensionally equivalent to `swap(target, last); take(last)`.

Once `ReceiveRemoval` is added, prefer the latter form because it visibly mirrors the returned target/last operation:

```rust
recv_slots.swap(target, last);
let removed = recv_slots[last].take();
```

This is a clarity/correspondence requirement, not a cryptographic change.

---

# 6. Required tests

Do not rely solely on existing tests passing. Add tests for the new proof-visible APIs and for the concrete positional invariant.

---

## 6.1 `protocol-core` Rust tests

Add tests covering:

1. `lookup_receive_key` finds every active sequence in a multi-key cache.
2. Lookup returns `None` for absent/consumed/unallocated sequences.
3. Lookup returns the unique current slot after a non-last swap-removal.
4. `finish_receive_with_removal` returns `None` removal for `Missing`.
5. It returns `None` removal and unchanged state for `Retained`.
6. Last-slot consumption returns `target_slot == last_slot`.
7. Non-last consumption returns the target and previous last slot and moves the previous last logical sequence into the target slot.
8. Old `finish_receive` and detailed finish always agree on state/disposition.
9. `restore_receive_key_with_slot` returns slots `0, 1, 2, ...` for sorted successful restoration.
10. Old and detailed restore functions accept/reject the same inputs and return the same projected state.
11. Existing capacity/exhaustion tests continue to pass.

---

## 6.2 Production receive tests

### Allocation lockstep

Derive several keys and assert for every active sequence:

```text
verified lookup succeeds
concrete returned slot is populated
recv_key(sequence) returns material
concrete occupancy == logical length
inactive tail is empty
```

### Non-last swap-removal

Derive at least four keys. Record **both key and nonce bytes** for the last sequence. Consume a non-last sequence. Verify:

- consumed sequence is absent;
- former last sequence now resolves to the consumed sequence's old slot;
- former last sequence has exactly the same key bytes;
- former last sequence has exactly the same nonce bytes;
- concrete occupancy decreases by one;
- positional invariant remains true.

### Last-slot removal

Consume the current last active sequence. Verify preceding slots do not move and the old last physical entry becomes `None`.

### Failed authentication and retry

For a future target requiring derivation:

1. derive/admit the target;
2. record control state, receive-chain state, concrete occupancy, slot mapping, and candidate/skipped key bytes;
3. complete with `authenticated = false`;
4. verify every recorded value remains unchanged after completion;
5. call `ratchet_recv_until` for the same target again;
6. verify receive-chain state does not advance — zero extra concrete KDF steps;
7. verify repeated failure remains neutral relative to the post-admission state.

### Replay

After successful consumption:

- verified lookup returns `None`;
- `recv_key` returns `None`;
- repeated completion returns `Missing`;
- logical state, concrete array, and receive chain are unchanged.

### Capacity/reuse

Fill all 50 slots and assert:

```rust
recv_slots.iter().flatten().count() == RECEIVE_CACHE_CAPACITY
```

Then:

- reject the next future receive without KDF advancement;
- consume a non-last key;
- verify occupancy becomes 49 and swap-removal remains aligned;
- admit exactly one next future sequence;
- verify the new concrete key occupies the newly available packed last slot;
- verify occupancy returns to 50.

### Exhaustion

Near `u64::MAX`, rejected advancement must leave:

- receive chain bytes unchanged;
- concrete array unchanged;
- control unchanged.

### Clone/reset

Clone a nontrivial manager, mutate one clone with a non-last consume, and verify the other clone retains its own sequence-to-key alignment and material. Reset/init must leave all concrete receive slots `None` and logical length zero.

---

## 6.3 Persistence tests

### Schema stability

Assert the serialized `RatchetManager` still has exactly the existing fields and `recv_past` remains a sequence-keyed map. Do not assert physical slot order in serialized output.

### Round trip after non-last swap-removal

Force a swap-removal, serialize, deserialize, and compare remaining concrete key and nonce bytes **by sequence**, not by physical slot.

Physical slot order is allowed to differ after restore.

### Internal divergence fail-closed

Add module-local tests constructing inconsistent internal managers and require serialization to fail for both:

```text
active logical slot + None concrete material
inactive physical slot + Some concrete material
```

### Capacity boundary

Exactly 50 persisted receive keys remain valid; a 51st is rejected through checked restoration.

---

# 7. Documentation updates after implementation

This section's original parallel-array documentation instructions are superseded. Current documentation must describe the code and proofs that exist after the refined-kernel follow-up.

### `crates/protocol-core/README.md`

State that:

- `RefinedRatchet<SendChain, RecvChain, Material>` owns logical control, both typed chain values, and the fixed material slots;
- the step callback `fn(&Chain, &[u8]) -> RatchetStep<Chain, Material>` is the sole opaque HKDF operation;
- the kernel owns admission, callback ordering, sequence/material lookup, retry retention, successful swap-removal, and paired restoration;
- `RefinedSendKey<Material>` keeps the send sequence and material together until consuming finish; and
- the older logical APIs remain only as proof-compatibility surfaces.

### `doc/formal-verification-stage-3.md`

Describe the structural invariant:

```text
active logical entry i <=> refined material slot i is populated
```

and describe live receive flow as:

```text
refined_advance_receive_until
    -> admission before callback
    -> one opaque step per admitted sequence
    -> atomic next-chain/material publication
    -> refined_receive_key by sequence
    -> authentication
    -> refined_finish_receive
    -> internal retention or swap-removal
```

Describe persistence as paired checked restoration through `start_refined_restore`, `refined_restore_receive_key`, and `finish_refined_restore`.

### `crates/protocol-core/proofs/trusted-boundary.md`

Record the refined kernel, callback boundary, paired restoration, consuming send token, and the generated/handwritten proof surface in the maintained inventory.

Preserve the remaining limitations. The parametric proof does not establish concrete HKDF semantics or output splitting, authentication-result provenance, serde correctness, hax/Rust/compiler correspondence, rollback resistance, crash atomicity outside the kernel call, zeroization, or physical key erasure.

---

# 8. What not to change

These are explicit scope and compatibility guardrails.

## 8.1 Do not change the receive protocol semantics

Do not change:

- `RATCHET_MAX_GAP` / `RECEIVE_CACHE_CAPACITY` = 50;
- counter semantics;
- future receive admission rules;
- total outstanding receive-key capacity;
- replay behavior;
- swap-removal semantics;
- admitted-future-before-authentication behavior;
- failed-authentication retention behavior.

A forged/admitted future frame may still advance the receive chain and cache keys before authentication fails. This refactor mechanizes the state correspondence; it does not redesign that behavior.

## 8.2 Do not change cryptography

Do not change:

- HKDF implementation;
- KDF output split;
- `SYM_RATCHET_INFO`;
- ChaCha20-Poly1305 behavior;
- CTX commitment construction;
- ratchet initialization offsets;
- any PQXDH primitive or transcript.

`Ratchet::ratchet` remains an opaque production primitive operation paired with one verified logical advance.

## 8.3 Do not refactor the send side

Keep:

```text
send_past
send_capabilities
advance_send / finish_send integration
```

out of scope except for compilation fallout caused by shared types/imports.

Do not use this PR to replace send HashMaps with arrays.

## 8.4 Do not change public sequence-facing APIs

Do not require external callers to pass physical receive slots.

Do not expose a stable public `ReceiveKey { sequence, slot }` capability solely for this refactor. Physical slots move under swap-removal.

Keep `recv_key(seq)`, `ratchet_recv_until(..., seq)`, and delete/complete behavior sequence-oriented at the public adapter boundary.

## 8.5 Do not change wire formats

Do not change:

- CryptoFrame schema;
- Cap'n Proto schemas;
- frame fields;
- sender/sequence encoding;
- associated-data construction.

## 8.6 Do not change the persisted schema

The external `RatchetManager` representation must remain the existing six-field structure. `recv_past` remains a sequence-to-key map.

Do not:

- serialize physical slots;
- depend on persisted map iteration order;
- make physical slot order part of persistence identity;
- introduce a storage migration just for this refactor.

After deserialization, a given sequence may occupy a different physical slot than before serialization as long as the concrete key material and logical sequence remain paired.

## 8.7 Do not return to a receive-side `HashMap`

A temporary serde `HashMap` while decoding the persisted sequence map is fine. The live `RatchetManager` receive cache must remain the fixed array.

Do not add a second sequence-keyed cache or index to make lookup convenient. The core logical array is the sequence namespace.

## 8.8 Do not treat slot numbers as stable identities

Never cache a slot across unrelated receive-cache mutations without revalidation.

Production should obtain current slots from:

- `advance_receive` for newly derived keys;
- `lookup_receive_key` for an existing sequence;
- `finish_receive_with_removal` for physical removal/movement;
- `restore_receive_key_with_slot` during restoration.

## 8.9 Do not perform a concrete KDF step on rejected advancement

The order must remain:

```text
verified logical advancement succeeds
    -> one concrete KDF step
```

not:

```text
concrete KDF first
    -> ask core whether it was allowed
```

If `advance_receive` returns no sequence/slot, concrete chain state and concrete slots remain unchanged.

## 8.10 Do not consume or move a concrete receive key on failed authentication

`Retained` must leave the entire post-admission logical/concrete receive state unchanged.

No swap, `take`, clearing, re-derivation, or replacement is allowed on authentication failure.

## 8.11 Do not weaken the proof boundary to make extraction easier

Do not add:

- `assume`;
- `admit`;
- lax F\* flags;
- new `hax_lib::opaque` annotations for the new core logic;
- handwritten generated-code edits;
- unproved lookup/removal contracts treated as axioms.

The purpose of this work is specifically to expose these decisions to the existing strict proof boundary.

## 8.12 Do not weaken or delete existing proofs/tests

New detailed APIs must project to the current logical behavior. Existing F\* lemmas and regression tests should remain valid or be mechanically adapted without weakening their claims.

If an existing theorem becomes difficult after the refactor, fix the implementation/proof composition rather than reducing the theorem.

## 8.13 Do not hand-edit generated proof artifacts

Regenerate:

```text
crates/protocol-core/proofs/fstar/extraction/*
crates/protocol-core/proofs/pro-verif/extraction/*
```

through the existing Makefile targets.

If generated ProVerif output changes only because dependency closure changes, inspect the diff and accept/update it through the normal inventory process. Do not add ProVerif model changes unless required by an intentional symbolic-semantic change.

## 8.14 Do not update inventory hashes prematurely

`reviewed-inventory.txt` is a review tripwire, not a way to silence changed-file checks.

Order:

```text
implementation
-> generated extraction
-> Rust tests
-> F*/ProVerif checks
-> inspect diffs
-> update only affected reviewed hashes
-> check-inventory/check-generated
```

If a hash changes for a file that is not changed by this work, investigate and document why before accepting it.

## 8.15 Do not broaden security claims

The completed refactor proves more about the **slot-control correspondence**. It still does not prove:

- HKDF computational security/correct implementation;
- libsodium primitives;
- serde itself;
- Rust compiler correctness;
- hax compiler correctness;
- crash/panic atomicity;
- persistent-state rollback prevention;
- concurrency/multi-replica atomicity;
- physical zeroization.

Keep those boundaries explicit.

---

# 9. Recommended implementation order

Implement the remaining work in this order.

## Phase A — protocol-core and F\*

1. Add `lookup_receive_key`.
2. Add `ReceiveRemoval` and `ReceiveFinishWithRemoval`.
3. Add `finish_receive_with_removal`.
4. Make old `finish_receive` a projection wrapper.
5. Add `ReceiveRestoreStep`.
6. Add `restore_receive_key_with_slot`.
7. Make old `restore_receive_key` a projection wrapper.
8. Re-export new APIs.
9. Add protocol-core Rust tests.
10. Add hax selectors.
11. Regenerate F\* extraction.
12. Inspect generated names/shape.
13. Add lookup, removal, wrapper-equivalence, and restore-slot F\* lemmas.
14. Run the proof suite before migrating production to the new calls.

## Phase B — production adapter

1. Replace `receive_key_slot` calls with `verified_ratchet::lookup_receive_key`.
2. Delete production `receive_key_slot`.
3. Keep allocation directly into `advance_receive.slot`.
4. Replace old `finish_receive` use with `finish_receive_with_removal`.
5. Apply returned swap/take operation exactly.
6. Strengthen concrete occupancy and failed-retry tests.

## Phase C — persistence

1. Add inactive-tail serialization rejection.
2. Migrate deserialization to `restore_receive_key_with_slot`.
3. Add divergence and post-swap round-trip tests.
4. Confirm serialized schema has not changed.

## Phase D — documentation and inventory

1. Update README/formal-verification text to describe verified lookup/removal/restoration decisions.
2. Update OR/AR/HB entries.
3. Regenerate all proof backends.
4. Run all verification gates.
5. Review diffs.
6. Update only affected inventory hashes.

---

# 10. Verification gates

Before the PR is considered complete, run at least:

```sh
cargo test --locked -p beaconcrypt-protocol-core
cargo test --locked
make -C crates/protocol-core verify
```

After reviewed generated/proof-boundary changes and intentional inventory hash updates:

```sh
make -C crates/protocol-core check-inventory
make -C crates/protocol-core check-generated
```

The PR description should report these commands/results, not only a generic `cargo test` run.

---

# 11. Completion checklist

## Core

- [ ] `lookup_receive_key` exists in `protocol-core`.
- [ ] Production no longer has `receive_key_slot` or another equivalent scan.
- [ ] `ReceiveRemoval` exists.
- [ ] `finish_receive_with_removal` is the sole implementation of logical receive completion.
- [ ] Old `finish_receive` is a projection wrapper.
- [ ] `ReceiveRestoreStep` exists.
- [ ] `restore_receive_key_with_slot` is the sole implementation of restoration append validation.
- [ ] Old `restore_receive_key` is a projection wrapper.
- [ ] New APIs are re-exported.

## Extraction/proofs

- [ ] New functions/types are hax-selected.
- [ ] Generated F\* was regenerated, not edited manually.
- [ ] Lookup soundness/completeness is proved.
- [ ] Detailed/compat finish equivalence is proved.
- [ ] Missing/retained `removal == None` is proved.
- [ ] Successful target/last removal shape is proved.
- [ ] Restore slot shape is proved.
- [ ] Detailed/compat restore equivalence is proved.
- [ ] All pre-existing ratchet lemmas still pass.
- [ ] No `assume`, `admit`, lax mode, or new opaque shortcut was introduced.

## Production

- [ ] Live receive cache remains `[Option<KeyMaterial>; 50]`.
- [ ] One successful `advance_receive` produces one concrete KDF step.
- [ ] Derived material is written to exactly the returned slot.
- [ ] Rejected advancement performs no KDF step.
- [ ] Existing receive lookup uses only verified `lookup_receive_key`.
- [ ] Failed authentication performs no concrete mutation.
- [ ] Successful authentication uses exactly the core-returned removal plan.
- [ ] Replay is state-neutral.
- [ ] Capacity/exhaustion behavior is unchanged.

## Persistence

- [ ] External six-field schema is unchanged.
- [ ] `recv_past` remains sequence-keyed externally.
- [ ] Deserialization uses slot-returning verified restoration.
- [ ] Serialization rejects missing active concrete material.
- [ ] Serialization rejects populated inactive concrete slots.
- [ ] Slot order is not persisted identity.
- [ ] 50-key boundary remains enforced.

## Tests

- [ ] Verified lookup tests added.
- [ ] Detailed removal-plan tests added.
- [ ] Restore-slot tests added.
- [ ] Non-last swap verifies key **and nonce** bytes.
- [ ] Last-slot removal test added.
- [ ] Failed future retry proves zero extra KDF advancement.
- [ ] Full capacity/reuse checks concrete occupancy.
- [ ] Replay checks concrete state neutrality.
- [ ] Clone divergence/independence is tested.
- [ ] Serialization inconsistent-active-slot test exists.
- [ ] Serialization inconsistent-inactive-slot test exists.
- [ ] Post-swap persistence round trip compares by sequence.

## Documentation/review

- [ ] OR-12 no longer lists production `receive_key_slot`.
- [ ] OR-14 describes slot-returning restore.
- [ ] AR-01 describes positional active/inactive invariant.
- [ ] AR-02 describes one HKDF result stored in returned advance slot.
- [ ] AR-04 describes exact core-returned swap-removal plan.
- [ ] AR-06 describes slot-aware restoration.
- [ ] HB-01 lists lookup/removal/restoration-slot lemmas.
- [ ] Docs do not imply HKDF/serde/compiler correctness is proved.
- [ ] Inventory hashes were updated only after implementation/proof diff review.

## Final commands

- [ ] `cargo test --locked -p beaconcrypt-protocol-core`
- [ ] `cargo test --locked`
- [ ] `make -C crates/protocol-core verify`
- [ ] `make -C crates/protocol-core check-inventory`
- [ ] `make -C crates/protocol-core check-generated`

---

# 12. Final expected trust boundary

PR #2 ended with the core returning physical decisions for a production-owned parallel array. The refined-kernel follow-up narrows the current receive-side correspondence to:

```text
extracted RefinedRatchet owns and preserves:
    logical control + opaque typed send/receive chains
    fixed sequence/material slots
    admission before the opaque step callback
    one callback output paired with each admitted sequence
    lookup, retry retention, and internal swap-removal
    atomic sequence/material restoration
    consuming send sequence/material tokens

production supplies and remains responsible for:
    concrete HKDF callback semantics and output splitting
    authentication-result provenance
    serde translation and surrounding persistence atomicity
    primitive behavior, compiler correspondence, and zeroization
    non-rollback ownership and peer-map selection
```

The index is no longer an adapter refinement relation. Sequence/material association, swap-removal, restoration, and mutation ordering are preserved structurally inside the same extracted kernel production executes; only the cryptographic and surrounding-system meanings of its opaque inputs remain assumptions.
