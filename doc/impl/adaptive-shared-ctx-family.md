# Adaptive CTX family with one shared hash cache

This HB-94 extension adds 78 checked statements in five modules: `AdaptiveCtxSharedHash` (12), `AdaptiveCtxSharedTarget` (12), `AdaptiveCtxSharedFamily` (17), `AdaptiveCtxSharedFamilyBounds` (19), and `AdaptiveCtxSharedPreparation` (18). They connect an actual selected-key CTX family with one common hash cache to the existing ordinary modified nonce-AEAD INT-CTXT and IND$ reductions. The independent raw nonce-AEAD all-key result remains separate: this extension does not yet supply all-key CTX adjacent hybrids, production evolving-key distributions, source material/reveal correspondence or the final computational-symbolic experiment.

## Actual source and complete state

The source interface has one selected key and N other key indices. At any index the adaptive caller can request uniform randomness, public hashing, sealing, or opening of arbitrary raw bytes. It sees actual optional plaintext replies and makes its final decision from the resulting transcript. Each decoder is a fixed public function of the supplied raw bytes. The selected key is sampled uniformly as 32 bytes; the source and reduction perform actual local cryptography for all known other keys. Other keys may coincide or be correlated with each other. They are parameters, or outputs of the displayed preparation, independent of the selected key's later draw. This distribution is an explicit component endpoint; it is not asserted for production evolving keys.

Each key has a `Local` history containing used nonces, successful seals, original public hash inputs, raw-attempt count and private commitment inputs. `SourceState` retains all these histories and one common `CtxRO.QueryCache`. Failed private lookups stay in this cache even if the optional opening reply is absent. Malformed raw input still increments the raw-attempt count. Sealing retains its original per-key nonce rejection and exact AEAD arguments. The full CTX commitment input remains the existing actual `outerInput` with its key, nonce, associated data and tag.

`install_separate` and `separate_install` reconstruct every canonical state field. `seal_interpretation`, `raw_interpretation` and `local_interpretation` show that the known-key compiler performs the exact canonical operation through the common hash interface. `linked_step` and `linked_schedule` extend this to every complete adaptive continuation, including final private state. `local_from_canonical` proves the inverse as a literal oracle-program equality, which supports resource bounds on actual programs rather than inferring costs from distributional equality.

## Selected challenger and shared cache

The reduction's other-key compiler performs actual local AEAD sealing/opening with its known key, then forwards its exact hash inputs to the selected CTX challenger's public hash interface. `forward` has no selected-key parameter. Its `forward_step`, `forward_schedule` and `forward_complete` laws preserve the target's complete private state while applying the exact shared cache and additional hash-observation effects. `cache_step` and `cache_schedule` retain the real shared cache when the extra analysis log is projected away.

Forwarding other-key private hashing creates additional entries in the selected challenger's public-hash instrumentation. These are legitimate requests of the constructed reduction, but they are not original selected-source public queries. `ReductionState.selectedPublic` therefore retains the original selected public history separately. `public_history_step` proves that this original history can be restored without changing the target reply, nonce history, successful seal log, raw count, private inputs or cache. The family `project` removes only the additional challenger instrumentation and restores that original history. It preserves the complete actual source state.

`linked_selected_run` and `selected_step` handle actual target requests. `linked_other_run` and `other_step` handle every other original index through the shared cache. The family `linked_step`, `linked_schedule` and `schedule_interpretation` establish full-state equality for arbitrary adaptive schedules. `initial_projection` identifies the original empty histories and single empty cache. `uniform_interpretation` includes the actual selected-key draw. `source_view_eq` then projects this established full execution to the caller's Boolean decision. Private proof histories and caches are not extra network, reveal, snapshot or persistence outputs.

## Constructed reductions and losses

Let H bound the selected reduction's public-hash traffic, S its original selected sealing requests, and R all selected raw attempts. The source cap is defined over every possible adaptive reply, including rejection, malformed input, replay and every accepted attempt. Require S < 2^96 for the existing constructive unused validation nonce. The prepared or fixed-key selected integrity hop is:

```text
Adv[actual selected CTX source, replay-only selected comparison]
 <= Adv_IND$[validationReduction(selectedDecode, crypto, client, H)]
    + H / 2^128
    + 2 * sum over i < R,
        Adv_INT-CTXT[indexedReduction(baseDecoder(selectedDecode), fallback,
                                      AdaptiveCtxReceive.wrapped(selectedDecode, client), i)]
    + R / 2^512.
```

The privacy hop additionally charges `Adv_IND$[viewReduction(selectedDecode, client)]` and ends at the existing random ciphertext-view comparison. `selected_integrity_bound` and `selected_privacy_bound` instantiate these terms on the exact family decision client after source interpretation. `prepared_integrity_bound` and `prepared_privacy_bound` instantiate them on the actual prepared client. The ordinary indexed forger stops at its selected raw-attempt slot. It never inserts a secretly recovered plaintext into an attacker-supplied target. The source receives its actual challenger-produced optional plaintext; the replay and random comparisons retain their previously proved interfaces and effects.

These are selected-key comparisons with no key/session selection multiplier yet. The H/2^128 secret-prefix term and R/2^512 commitment term use the existing programmable classical random-oracle model. This is stronger than collision resistance for BLAKE2b-512 and remains explicit. Correct ordinary primitive interfaces, including the existing AEAD contract and actual functional local operations, remain trusted. No new protocol authentication or freshness event is assumed as a primitive winning event.

## Preparation and generation order

`Prepared` contains the exact context and finite family of other keys. The arbitrary probabilistic `prepare` has no selected-key input. The actual `source` runs this preparation first, then the selected uniform draw and full family schedule. The ordinary reduction performs the same preparation with its own uniform queries after the challenger's target generation. `canonical_uniform` proves that those preparation queries preserve all selected challenger state. `prepared_interpretation` applies the independent sampling interchange to the entire retained preparation and continuation, including the final full source state. It does not rely on equality of marginal key distributions.

`prepared_view_eq` gives the original decision's evaluated equality with the ordinary canonical wrapper. `independentSetup` is a concrete preparation that draws the uniform finite function from N indices to 32-byte keys. `independent_setup_bound` charges 32N byte-valued draws. Coincident values remain in both the distribution and state; no inverse lookup from key bytes or injectivity premise is used. The source costs are proved separately on its original program.

## Query and byte ledger

Let P bound the preparation's uniform queries and U bound caller uniform queries across every key. Let B bound the total selected plaintext bytes submitted to sealing, including requests rejected by nonce validation. Every bound quantifies over all possible reply continuations. Define W = P + U + 64(H + S + R).

| Actual operation | Checked cap |
| --- | --- |
| Prepared source uniform requests | P + 32 + U + 64(H + S + R) |
| Each prepared indexed INT-CTXT forger | W uniform requests; S selected seals; one ordinary final verification |
| Prepared validation reduction | W uniform requests; S + 1 selected seals; B plaintext bytes |
| Prepared ciphertext-view reduction | W uniform requests; S selected seals; B plaintext bytes |
| Complete real validation or view experiment | 32 + W uniform requests |
| Complete random validation experiment | W + B + 16(S + 1) uniform requests |
| Complete random ciphertext-view experiment | W + B + 16S uniform requests |
| Independent preparation | P = 32N byte-valued draws |
| Independent full source | 32(N + 1) + U + 64(H + S + R) uniform requests |

`local_step_bound` and `local_schedule_bound` charge actual known-key forwarding. `forward_bound` and its four exact class laws show that this forwarding makes hash and uniform requests but no selected seal or raw request. `forwarded_local_bounds` retains all other-key hash work. The family `target_step_bound`, `wrapped_target_bound`, `forward_resource`, `route_step_bound` and `wrapped_route_bound` transfer these caps through the full adaptive source.

`uniform_route_exact` identifies U with the original uniform requests at every key. `hash_route_exact` identifies H precisely as all original public hashes plus other-key seals and raw attempts. `family_union_bound` and `hash_route_bound` derive H <= Hpublic + Sother + Rother from the original separate caps. Thus H + S + R includes all public hashing and all keys' seal/raw work; the selected private lookup is charged separately exactly where it occurs. Rejection can reduce actual work but never removes a submitted request from the bound.

`canonical_uniform_bound`, `wrapped_budgets`, `decision_budgets` and `source_uniform_bound` establish source and wrapper costs. `indexed_forger_bounds`, `validation_bounds`, `privacy_bounds` and the four fixed-key real/random experiment bounds instantiate the existing ordinary query ledgers. `no_target_seal_plaintext`, `plaintext_step`, `wrapped_plaintext_bound` and `decision_plaintext_bound` preserve the weighted plaintext cost. The validation seal submits an empty message and adds only its 16-byte random tag.

`lift_no_class`, `lift_uniform_bound`, `prepared_class_bound`, `prepared_uniform_bound` and `prepared_budgets` account for setup in the actual reduction. `prepared_source_uniform` establishes its separate original-source cap. `prepared_plaintext_bound`, `prepared_decision_budgets` and `prepared_decision_plaintext` retain all query and byte caps after projection to the original decision. `prepared_reduction_bounds` and `prepared_experiment_bounds` state the complete displayed ledger. `independent_source_bound` includes every concrete key draw.

A caller's arbitrary finite uniform-oracle request counts once; sampled bytes use one byte-valued query each. The bounds are oracle-query counts, not a compiled runtime theorem. Other-key AEAD work, parsing, histories, function updates, copying and setup computation remain in the constructed reduction. Their counts follow original other-key seal/raw traffic and their sizes follow submitted inputs; zero selected primitive calls does not make that work free.

## Remaining integration

All-key CTX hybrids must interpret processed keys' private dictionaries and unprocessed keys through this same common public cache. They must retain failed lookups and identify consecutive games in one original indexed experiment before telescoping. The native material interpretation must route source labels without assuming byte-value injectivity. The evolving KDF composition must justify the target distribution while preserving repeated derivations, both directions, skipped and consumed material, actual reveal replies and copied/restored ownership. The position/source and final symbolic capability interfaces remain separate required links. This milestone does not establish the final BeaconCrypt security claim.

## Focused validation

All five final modules and their 78 persistent dependency guards pass direct Lean checking without diagnostics. The full combined library passes 3,304 jobs. Policy, root-import, reviewed-inventory and whitespace gates pass with 254 handwritten Lean modules and 418 reviewed artifacts; all prior 413 paths and their order are retained. Fresh formatting and all 16 transcript-fidelity tests pass, with the fidelity suite taking 12.43 seconds. The current `origin/vcvio` was fetched and directly verified as `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. Independent mathematical review covers the full shared-cache and original-history projection, actual setup/target generation law, ordinary endpoints and complete query/byte accounting. There are no Rust or ProVerif changes, so no full Rust mutation run is required under the current user instruction. These results validate the stated selected-key component and do not replace the final complete matrix on the eventual closed protocol composition and exact integration merge.
