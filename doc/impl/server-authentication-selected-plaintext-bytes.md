# Source-derived plaintext-byte budget for authentication

`PqxdhServerAuthCtxByteBounds` closes the weighted resource obligation for the actual ordinary CTX authentication client. Its sixteen statements prove `client_plaintext`: the complete `CtxExperiment.client`, including its context and residual sampling and every adaptive API reply, submits at most `Usize.max` plaintext bytes to the selected encryption endpoint. The limit follows from the existing source overflow gate and the proved one-selected-seal control. No caller payload-size, successful-execution, freshness or honesty premise is added.

The bound is deliberately conservative. `Usize.max` is the maximum of the source machine-sized unsigned integer in the extracted model, not a practical deployment message-size recommendation or a runtime bound. It is used symbolically; the theorem does not silently replace it by a chosen architecture width. The counted plaintext includes the exact eight-byte assigned-ID binding prefix. Known-key encryption remains actual local work and submits no body to the selected challenger.

## The literal builder enforces each request's limit

The source Server builder checks that the chosen application payload is nonempty and that `8 + payload.length ≤ Usize.max` before its allocation callback and first seal. `Sized` records the resulting full-context plaintext limit. `candidate_bounded` follows every identity, reservation, initializer, length, allocation and binding branch of `PqxdhInitialGenericBuilder.candidate`. A reached binding has exactly eight bytes by the existing source binding theorem, so the precise concatenated plaintext satisfies the original overflow check. Rejected branches issue no seal.

`build_bounded` retains this property through next-ID allocation, pending-token Server-binding and peer-availability checks. `program_bounded` transports it to the actual material builder oracle program. These statements use the already proved context-preserving send driver. They quantify over every possible service reply, rather than condition on a successful writer or final response.

## Actual compiler and all adaptive callbacks

`Oversized` identifies a selected component request whose submitted plaintext exceeds the source limit. `oversized_seal` proves that such a request must be a selected seal, and `no_seal` therefore rules it out for every zero-selected-seal program. Hashes, raw opening attempts, uniform requests and known-key calls cannot acquire a selected plaintext charge.

`sealer_bounded` follows the literal selected/known sealing adapter. A selected query carries exactly the pending source context's plaintext. Known material uses the real local path; invalid associated-data width, nonce refusal and optional writer failure remain unchanged. `compiler_bounded` relates an oversized component request to a violating source sealing context. `compiled_bounded` combines that all-reply implication with the source program's zero-violation theorem through the actual optional stateful compiler. No source or component state is discarded to obtain a cost result.

`build_route_bounded` follows the actual pending-token lookup and selected/ordinary mark dispatch, including the complete source log and settlement. `route_bounded` covers all original API calls: build uses that concrete proof, and the existing actual per-route seal bills establish zero selected seals in every other route. `handler_bounded` preserves the result through designation and sticky-refusal settlement. `stopped_bounded` handles every adaptive continuation under the actual stopping wrapper, including calls made before refusal. No caller-supplied source invariant is needed for this per-request size property.

`client_bounded` includes the literal context and residual samplers. Their actual uniform calls have no selected seals. The resulting zero-oversized theorem therefore describes the exact complete client used by the published authentication event and ordinary reductions.

## Weighted total and random challenger

`cost_nonseal` proves that every nonselected-seal request has plaintext cost zero. `weighted` combines a per-request source size gate with a syntactic selected-seal count. Its induction charges the actual submitted plaintext length at each request and preserves the remaining budget through every possible oracle reply. It proves the weighted `AdaptiveCtxDynamicKnownBounds.PlaintextBound`, rather than only bounding individual messages or successful records.

`client_plaintext` instantiates that result with the actual client's proved selected-seal cap of one. Thus the total selected plaintext-byte budget is `Usize.max`, without any external byte-count premise. The source cap counts attempted seals even if the component refuses or a writer later fails.

The exact ordinary observer and known-key wrapper already preserve this weighted metric. Applying `PqxdhServerAuthCtxPrimitiveResources.validation_random_uniform` with this theorem gives the actual random validation challenger uniform budget `B + Usize.max + 32`, where `B = H + 64*(H+2)` and `H = U+76` retain the previously proved complete source and digest-sampling bills. The final32 is at most two random tags; this random experiment samples no hidden encryption key. The two real challengers retain their separately proved `32+B` bills. This module changes no reduction, advantage term or target-selection factor.

## Scope and checks

This is an operational resource proof for the same `revealSeed=false` client and its existing primitive, ROM, codec and compiler contracts. It proves neither primitive internals nor serialization-library behavior, allocator correctness, runtime complexity, saved-state or persistence properties. All sixteen theorem reports are guarded; direct module checks and independent semantic reviews precede publication. Central imports, inventory and aggregate checks belong to the enclosing reviewed integration.
