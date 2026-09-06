# Complete source receive with interpreted material

`RawCtxInterpretedReceive` adds 27 guarded statements connecting a generic material-label receive program to the actual extracted receive driver. The interpretation may map different labels to the same material. It changes no chain, control, request, target, context, slot-presence bit or sequence tag. The result includes the complete source kernel, actual optional reply and full primitive poststate.

This continues [noninjective material and opening interpretation](source-material-interpretation.md). It supplies the complete receive-effect computation. A concrete hidden-key label-table interpreter, its KDF/opening equations and the surrounding raw/whole-owner/send schedule still need to be constructed.

## Source operations and totality

`Kdf` and `Effect` carry the same fields as the existing source capabilities, with material as a parameter. `beginReceive` and `resume` follow the extracted source bodies, including zero-count rejection, final-step validation, skipped-slot access, array bounds, capacity checks and staged publication. `resume` consumes its supplied RustM chain/material step at the original source point. Its failure or divergence remains a diagnostic source result; it is not converted into ordinary API rejection.

`native_begin` and `native_resume` identify the actual extracted functions at native material. `begin_map` and `resume_map` preserve those complete source computations under arbitrary material interpretation. The latter accepts any supplied RustM step and maps its actual chain/material result without an injectivity assumption.

`resume_progress` proves totality for every typed chain/material reply, preserves the saved entry and strictly decreases the remaining KDF count whenever another KDF capability is produced. `begin_total` proves unconditional admission totality and entry retention. `finish_total` uses the existing generic cached/future publication proofs and returns the callback's exact optional reply. These are ordinary source/control facts; none requires decryption correctness, a valid initial kernel, honest replies or a fixed functional KDF.

`normalResume_exact`, `normalBegin_exact` and `normalFinish_exact` justify the private normalizers by equality to the source RustM results. They select only already proved unique successful results. `normalResume_rank` proves the strict measure used by `program`; the finite driver has no fuel parameter or fallback branch. These normalizers are proof interfaces, not newly executable Rust implementations.

## Complete callback interpretation

`ReceiveSpec` retains the unchanged KDF request and private selected opening capability. Its KDF response is an actual chain paired with a material payload. The program executes all requested callbacks and publishes exactly their returned optional result.

`normalResume_map`, `normalBegin_map` and `normalFinish_map` lift the source mapping through the exact normalizers. `program_map` then proves complete adaptive equality in any lawful monad: interpreting the initial effect and using compatible value callbacks equals interpreting the complete result of the label program. `receive_map` includes source admission. Taking the monad to be a state transformer retains every primitive/cache effect, including effects from a failed opening.

The two compatibility equations are explicit. The value KDF response must equal the interpretation of the actual label KDF response, preserving its chain. The value opening handler on the interpreted private capability must equal the label opening handler on the original capability. These are local operational realization obligations. The theorem does not assert them for a newly sampled evolving-key table or arbitrary unrelated callbacks. The supplied interpretation is a fixed mathematical function for this comparison and may be noninjective.

## Actual native receive

`decodeResponse` applies the existing total conversion of the complete typed native 76-byte KDF response. `decodeResponse_exact` records that actual conversion. `normalResume_native`, `normalBegin_native` and `normalFinish_native` identify the existing source normalizers and native kernel wrapper.

`nativeAdapter` forwards the original native KDF request, obtains its complete response and only then decodes it. Its opening branch forwards the actual private native capability. `program_native` and `receive_native` give literal oracle-program equality with the existing `RawCtxOwnerOracle` program and receive operation; source queries and all continuation replies are retained.

`receive_interpreted` composes this native compiler with the general material theorem. Compatible native typed callbacks and label callbacks therefore produce the original source receive result after kernel interpretation. `receive_state` makes the full primitive poststate explicit. No final primitive cache or failed lookup is discarded. The opening equation still concerns the selected private capability; a particular key/nonce/context getter backend must discharge it using the already proved opening getter/interpreter laws.

## Query costs and scope

`program_kdf_bound` bounds all possible generic KDF calls by the source rank: remaining plus one for a KDF capability, zero for other effects. This is a conservative allowance, including malformed represented pending states. It is not a new claim that ordinary admitted source calls require 52 callbacks, and it does not replace the existing sharper 51-call native admission bound. `program_open_bound` allows at most one actual opening callback for every possible reply. `receive_query_bounds` preserves every selective underlying query bound under the compatible complete stateful interpretation.

The query equalities count oracle work only. Native control, array copying, response conversion, label interpretation and callback implementations still perform local work. There is no runtime, memory, constant-time, parser traversal, panic/unwind, crash or compiled-library trace theorem here.

The component does not generate labels, hide keys through an inverse lookup, establish key independence or prove an evolving-key distribution. Concrete label realization, opening getter/primitive dispatch, source send and whole-owner routing, mixed schedules, reveals, restored or copied state and global security remain separate obligations. Private source state and material labels are not added to public, reveal, snapshot or persistence interfaces. Actual optional plaintext is retained; its declassification belongs to the outer experiment. No authentication or ideal-opening premise is introduced.

## Focused validation

The final module and all 27 persistent dependency guards pass direct Lean checking without diagnostics. The complete library passes 3,287 jobs; the direct root and policy checks pass. Reviewed inventory and an independent rehash pass for 237 handwritten Lean modules and 401 unique artifacts, preserving all 400 prior paths and their order. Independent direct review checks the final module and all guards, with separate semantic review of the native compiler, callback equations and full-state/query corollaries.

Fresh source transcript fidelity passes all sixteen tests in 11.90 seconds. Formatting, whitespace and forbidden-placeholder/custom-axiom checks pass. Fresh Rust 1.96 workspace Clippy completes in 0.83 seconds with the existing 38 library warnings and two additional test warnings. The original pinned vector setup remains unchanged. Development elaboration diagnostics were resolved by explicit response types, complete state-monad types and narrow source rewrites; no placeholder, suppressed check or new premise remains in the final proof.

Fresh fetched and direct `origin/vcvio` both identify `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of the topic. No Rust or ProVerif source changed, and the current user instruction requires no new full mutation run for this proof/documentation milestone. Earlier runtime, finite-family symbolic and mutation results remain evidence on their unchanged inputs; this checkpoint does not report a new persistent symbolic result or completed global verification matrix.
