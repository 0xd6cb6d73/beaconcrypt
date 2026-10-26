# Complete source send with interpreted material

`RawCtxInterpretedSend` adds 23 guarded statements connecting arbitrary material labels to the actual source send-effect driver. Different labels may denote the same material. The source chains, control, saved entry, request, sequence, logical capability and private context retain their original values. This continues [complete receive interpretation](source-interpreted-receive.md), allowing the two operation-level interfaces to use the same material interpretation without assuming key-byte uniqueness.

## Actual source operations

The generic `Kdf`, `Seal` and `Start` carry the original source fields, parameterizing only material payloads in the saved/advanced kernel and selected seal. `beginSend` follows every extracted admission check. `resume` uses the supplied chain/material result at the original source point. `finish` invokes the original logical finish function before returning the advanced kernel and actual optional result.

`native_begin`, `native_resume` and `native_finish` identify the complete extracted native computations. The source mapping includes RustM failure and divergence when the supplied resume step has such an outcome; neither diagnostic is relabelled as an ordinary API `None`. `begin_map`, `resume_map` and `finish_map` preserve these computations under an arbitrary noninjective material map, including all retained receive slots.

`begin_total` proves total admission for every represented generic kernel. `ready_exact` identifies the precise capability produced by every supplied typed chain/material reply. `finish_exact` proves that either logical capability state returns the advanced kernel and exact optional reply. An active failed seal therefore retains source advancement; it does not restore the saved send entry. An exhausted admission makes no KDF or seal callback. Empty application input is checked by the outer owner helper and is not attributed to this generic opaque-context admission function.

## Complete finite interpreter

`normalBegin_exact` justifies the private admission normalizer using the already proved unique source result. `normalBegin_map` and `ready_map` carry material interpretation through admission and the actual response. The finite `program` performs its requested KDF callback, constructs that response's selected seal, invokes the actual optional seal and returns the advanced kernel. There is no fuel parameter or extra fallback.

`program_map` proves whole-program equality in an arbitrary lawful monad under two explicit callback equations. The value KDF response must be the interpretation of the label response with the same chain; the value seal on the interpreted private capability must equal the label seal on the original capability. `send_map` includes the actual source admission. The interpretation is a fixed mathematical function for this comparison; the theorem does not choose labels or construct these callback implementations.

`normalBegin_native` and `ready_native` identify the original native normalizers. `nativeAdapter` forwards the unchanged source KDF request and its complete typed 76-byte response, using the existing checked response decoder, then forwards the selected native seal. `program_native` and `send_native` give literal oracle-program equality with the published source send driver. They preserve original query order and every actual optional reply.

`send_interpreted` composes the native compiler with the arbitrary material theorem. It retains the original source result under the explicit native/label KDF and seal equations. `send_state` exposes the complete primitive poststate, including effects of a failed seal. No cache, auxiliary state, source kernel field or returned option is discarded.

## Budgets and remaining realization

`program_kdf_bound` and `program_seal_bound` permit at most one source callback of each category, for every possible typed or optional reply. `send_query_bounds` preserves every selective underlying oracle-query bound of the compatible complete stateful computation. These are query budgets; source control, state/array copying, response conversion, material interpretation, logical finish and primitive execution remain local computation. No native timing, allocation, memory, constant-time, panic/unwind or library implementation equality follows from these bounds.

The callback equations are operational obligations for a concrete label realization. There is no inverse key lookup, injectivity premise, fixed KDF reply law, independent key distribution, fresh nonce premise or ideal sealing/decryption assumption. A particular key/nonce/context getter and primitive backend must discharge the equations. Whole-owner/raw/mixed scheduling, actual label generation, reveals, copied/restored ownership, source runtime contracts and global cryptographic composition remain separate work. Private contexts, labels and source state are not newly exposed through public, reveal, snapshot or persistence interfaces.

## Validation

The focused candidate passed the full 3,288-job Lean build, direct root and policy checks, all 23 persistent dependency guards, and the 238-module/402-entry inventory with every fingerprint independently rehashed and the preceding 401 paths in their original order. Independent review directly checked the final module and all 23 guards and approved the source, state, query and documented realization boundaries. Fresh source-fidelity validation passed all 16 tests in 12.45 seconds; formatting and Rust 1.96 workspace/all-target/all-feature Clippy passed, with Clippy taking 0.75 seconds and retaining the existing warnings. Diff and placeholder scans passed. Runtime, symbolic models and tests are unchanged; no mutation suite was rerun for this proof-only change under the current user policy. These checks validate this focused interpretation interface and do not establish the remaining label realization or global protocol security.
