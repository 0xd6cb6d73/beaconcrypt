# Source material labels and native opening interpretation

This HB-91 extension adds 24 statements in `RawCtxMaterialInterpretation` and nine in `RawCtxInterpretedOpening`. It establishes an exact payload interpretation boundary for the extracted ratchet slots and the native opening object. A private label may stand for actual key/nonce material without requiring distinct labels to have distinct byte values. The result is a functional source equation under a stated callback equation, before any key-distribution or security hybrid.

## Actual source slots and publication

`mapRefined` keeps the original send/receive chains, counters and source control. It maps only present cached material payloads and retains every slot's sequence tag. `mapPending` likewise preserves the committed control, final chain, target sequence, first slot and skipped count while mapping the staged material. The arbitrary function `interpret` may be noninjective. Nothing chooses a unique label from key bytes or excludes accidental equality between different positions or owners.

The 24 source statements cover the following exact operations:

| Statements | Checked behavior |
| --- | --- |
| `mapArray_index`, `mapArray_set`, `mapArray_update`, `mapArray_get`, `array_ext` | Actual fixed-array access and updates commute with interpretation, with original bounds and failure results. |
| `mapOption_elim`, `option_as_ref`, `option_take`, `rust_map_ok`, `option_is_some_map` | Optional presence, borrowing, taking and successful result mapping retain their original source behavior. |
| `receive_key_map`, `prepare_cached_map` | Actual tagged lookup and cached preparation keep control, missing/mistagged rejection and prepared indices. |
| `publish_cached_map` | The actual cached publication clears the same selected slot and moves the same remaining state. |
| `publish_future_slots_map`, `publish_future_map_bounded`, `publish_future_rejected`, `publish_future_map` | Actual future publication copies and clears the same slots, preserves both returned arrays, and handles both admitted windows and malformed-window rejection. |
| `empty_slots_body_map`, `empty_slots_map`, `pending_slots_body_map`, `pending_slots_map`, `pending_valid_map` | Complete extracted validation loops and pending validity have identical results, without assuming a valid entry or transaction. |
| `empty_material_map`, `from_counters_map` | Actual empty-slot construction and initialization with supplied chains/counters commute. |

The loop and publication laws use the extracted generic source functions and their existing exact-loop results. They do not introduce a replacement receive state machine or change the source window. Array errors and malformed transactions retain their complete `RustM` results.

## Opening and complete callback effects

The thin `Opening` record stores the original refined entry, immutable context and cached/future prepared transaction. Its material getter follows the native opening object's prepared slot directly, including index bounds and sequence-tag checks. It does not substitute a fresh control lookup for that operation. On an absent material it issues no callback; otherwise it passes the selected material, prepared sequence and original context to one callback. Actual cached/future publication follows the returned optional reply; `None` restores the original entry.

| Statement | Checked behavior |
| --- | --- |
| `native_finish`, `native_sequence`, `native_material` | Specialization is exactly the extracted native object's finish and getters. |
| `finish_map`, `sequence_map`, `material_map` | Arbitrary payload interpretation retains publication, prepared sequence and optional getter results, including malformed cases. |
| `run_map` | The complete thin interpreter commutes with interpretation under the explicit callback equation. |
| `native_run` | The concrete specialization uses the actual extracted material, sequence and context getters and finish, in source order. |
| `native_run_map` | A label callback gives the same complete native source result and effects after interpreting its private payloads. |

The callback equation is `native (interpret label) sequence context = labelled label sequence context`. Both sides may run in any lawful monad, including `StateT` over the entire primitive cache and auxiliary state. The theorem maps only the returned source kernel payloads and preserves the actual optional reply and every callback effect. It therefore includes failed commitment/AEAD attempts and their retained primitive state when those operations instantiate the callback. The equation is an explicit local implementation obligation, not a new cryptographic assumption or an assertion that an unknown key can be recovered. A later selected-key reduction must discharge it through its actual oracle routing.

The harness preserves source `fail` and `div` as diagnostic result constructors; it never turns them into ordinary API rejection. This result encoding does not establish runtime termination or execute a diverging native program in finite time. Existing source totality results and the complete owner adapter must provide the native execution connection where needed.

## Remaining source and security composition

The original chains remain concrete, and the surrounding KDF begin/resume and whole-owner schedule are not erased by these statements. A full label-based source interpreter must establish those additional operational equations and preserve generated labels through every callback, retry, reveal, initialization and supported restore. The existing fixed-source position theorem supplies a separate material-origin relation; it does not imply the independent key-family distribution of an ideal experiment.

Labels, interpretations, full kernels and private proof histories are analysis context, not new public replies, compromise values or persistence fields. This boundary does not infer nonce freshness, key independence, collision bounds, source authenticity, post-compromise recovery or a global one-key/multi-key security theorem. Local material mapping, array copying, source validation and cryptographic callback work are still real work. No new runtime or oracle-query bound is asserted by this checkpoint. Native primitive, compiler, library, codec, storage and resource correspondence retain their existing scope.

## Focused validation

Both final modules and all 33 persistent dependency guards passed the full locked Lean build (3,286 jobs), and an independent direct check of the same two modules completed without diagnostics. The direct root import, Lean policy, inventory, formatting and whitespace checks passed. All 400 unique manifest entries were independently rehashed with the previous 398 paths and order preserved; the added scope is two modules, 236 handwritten Lean files and HB-91's 393 operational statements. Existing source and runtime module bodies are unchanged.

All sixteen transcript-fidelity tests passed freshly in 12.65 seconds. The Rust 1.96 workspace Clippy command with all targets and features passed freshly in 12.60 seconds, using the already initialized pinned test-vector submodules. A fresh private fetch and direct remote query both returned `8330cdef4f4659931b6764a026cd90c4caf833a4` for `vcvio`, which remains an ancestor. No Rust or ProVerif input changed, and no mutation rerun was required by the user's proof-only testing policy. The focused results establish the displayed source equations; they do not provide a new symbolic classification, a cryptographic advantage bound or the final source/global validation matrix.
