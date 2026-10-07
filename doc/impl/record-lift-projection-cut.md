# Selected32 cuts of a persistent full76 miss

`PqxdhRecordLiftProjectionCut` establishes sixteen statements about one actual lazy-table miss and its next ratchet derivation. This is a component of the ordered evolving-chain proof. It does not establish that an arbitrary real HKDF reply is uniform, that the World reaches this cut with the required earlier-hybrid distribution, or that its complete source continuation has the masked interface used here. Those source joins remain explicit work.

`Part.chain` selects the second32 coordinate, retaining key32 and nonce12; `Part.key` selects first32, retaining chain32 and nonce12. `split` is an equivalence of all76 bytes. `restore_split` and `split_restore` retain all correlations, and `split_uniform` and `split_continuation` factor the uniform full76 sampler under an arbitrary complete continuation. No repeated projection is independently sampled.

A private `Mask` contains the complete pre-miss table, the selected coordinate, the other44 bytes, and the exact post-miss lookup/draw counters. `realize` reconstructs the selected full reply and the complete updated table using only the chosen target32. `realize_mask` proves that reconstruction exactly. `miss_continuation` applies the existing lazy cache's actual miss branch, requiring that the selected coordinate was absent. It preserves every answer, cache entry and counter under the same full continuation. It is not merely equality of key marginals.

`AtMiss` packages that operational absence fact. The sample of the source context and `AtMiss` state executes before the cache draws its new76 bytes. `observed` runs the actual lookup and supplies only the private mask to the continued observer; `observed_delayed` proves that the chosen32 may instead be sampled after the entire observer result. The pre-miss context may contain prior private cache values, including byte aliases, but cannot depend on bytes not yet sampled. The masked observer must not receive the selected newly drawn coordinate through another state copy. Proving the global source continuation has precisely this interface is not assumed or discharged by defining `Mask`.

`candidate_bound` uses this complete unconditioned distribution to bound membership in the observer's returned list by `qCandidates / 2^256`. Repeated candidates are charged in the list length. This is a guessing bound at this explicitly uniform masked cut, not the old public-HKDF/random-table or root-query interpretation. Connecting all actual source/public candidates, their costs and the refusal event to this collector remains necessary.

`childReal` performs the literal persistent full76 miss and evaluates the production ratchet expansion on that same output's second32. The observer receives the retained private mask and the child full76 output. `unitObserver` samples the prior context and retained44 itself. `child_source` commutes these independent samplers under the complete continuation, identifying the actual cut with the existing source endpoint whose primitive sampler is exactly `PqxdhServerAuthKeySchedule.uniform32`, with Unit context. `child_independent` gives the corresponding ideal child-output game, discarding only the unused primitive input draw. No new sampler-specific Extract assumption is introduced.

`child_bound` then applies the existing full-output reduction: one coefficient-one Extract advantage for the ordinary uniform32 sampler, plus one coefficient-one uniform-secret-key HMAC PRF advantage. The explicitly constructed reductions are `fullExtractReduction hmac .ratchet (unitObserver sample observe)` and `fullExpandReduction .ratchet uniform32 (unitObserver sample observe)`. Both act on the same retained-context observer. The only functional contract is the existing `SourceFullCorrect`; the security endpoints remain ordinary Extract-on-uniform32 and two-query HMAC PRF. All public/local HKDF evaluations in the observer remain real. The theorem supplies no source alias, nonce uniqueness, authentication or global secrecy conclusion by itself.

The resource premises bound the entire prior sampler by `qSample` and every local observer continuation by `qObserve`. These bounds are explicit hypotheses, not declarations that ambient work is free. Deterministic local evaluations remain part of the reduction's runtime even though they issue no challenge-key oracle query.

| Computation | Uniform-oracle query cap |
| --- | --- |
| Retained private context | `qSample + 44` |
| Primitive observer | `qSample + 44 + qObserve` |
| Actual miss followed by child | `qSample + 76 + qObserve` |
| HMAC reduction, excluding its challenger | `32 + qSample + 44 + qObserve` |
| Real Extract game | `32 + qSample + 44 + qObserve` |
| Uniform Extract game | `32 + 64 + qSample + 44 + qObserve` |
| Real HMAC challenger game | `64 + 32 + qSample + 44 + qObserve` |
| Random HMAC challenger game | `32 + 64 + 64 + qSample + 44 + qObserve` |
| Ideal child-output game | `qSample + 44 + 76 + qObserve` |

`reduction_bounds` also proves the HMAC challenge-query cap of two. The unused32 primitive-sampler draw in the HMAC reduction is charged. Both random64 HMAC answers are fully charged even though only12 bytes of the second answer contribute to the source output. The logical source table lookup increments once and its miss counter once, as retained by `realize_mask`; global lookup limits and all record/hash/AEAD effects must still be supplied by the World compiler and query-accounting theorems.

Direct checks use Lean4.34, an owned dependency overlay, the coordination queue, a180-second limit and `-j1 -M8000`. The sixteen exact axiom guards allow only `propext`, `Classical.choice` and `Quot.sound`. The module uses the existing VCVio probability compatibility API for its complete-distribution lemmas; its deprecation warnings are not suppressed. Independent semantic review approved the exact source; the guarded module, root import, inventory and transcript-fidelity checks passed. The latter ran20 Python and30 Rust tests. Final publication hygiene remains a separate gate. No Rust, primitive implementation, persistence or snapshot proof is involved.
