# Actual unsigned Phase1 and native registration projection

`PqxdhServerAuthPhase1Projection` connects the original attached-verifier outputs to the four unsigned fields of the extracted `pqxdh.InitKex`, its original validator, and the native pending registration ID. The complete journal consumer retains the same actual decoded request and consumed token established by [target identity attribution](server-authentication-phase1-target-identity.md). It does not identify raw signature buffers or recover a root from the cleared pending field.

## Exact source equations

`source_fields` follows the original identity parser, three attached-verifier calls and three typed payload parsers. The successful verifier replies are precisely the tagged prekey, one-time key and ML-KEM public key represented by the returned typed tuple. This statement allows an arbitrary verification function. It needs neither the signature adapter nor a uniqueness law for signatures.

`unsigned` constructs the fixed-width native unsigned `InitKex` from those typed values and the original tags. `unsigned_bytes` and `source_unsigned` recover the exact original identity bytes and verifier replies. `unsigned_validates` then executes the original extracted `validate_init_kex` and returns the unchanged native `VerifiedInitKex`. The proof consumes the maintained concrete untagging refinements; it introduces no cryptographic or codec injectivity premise.

`decoded_unique` identifies two successful receipts for the same raw request under the same decoder, getters and verification function. This is determinism on the same input. Different raw inputs, encodings and signatures may still yield the same typed result.

## Same pending occurrence

`token_fields` joins that deterministic verification receipt to the actual `TokenReceipt`. It derives the original Server binding, native Beacon identity, and registration ID, including the equality to the original core `registration_id` operation. The registration-ID bytes are exactly the verified raw Beacon identity followed by the verified one-time public key. `context_registration` specializes these equations when the actual identity and verified tuple equal the target context's fields; that equality is explicit in this local theorem.

`Projected` groups these functional equations with the exact unsigned verifier outputs and extracted validator result. `token_projection` establishes every conjunct from the same source receipt. It does not impose a cryptographic freshness or origin property.

## Complete journal consumer

`journal_projection` starts from the actual context sampler and a supported normal execution of the complete observed, stopped source API. It retains the existing accepted-owner, no-refusal, no-collision and actual successful owner-build conditions. The source identity and pending provenance come from that execution. The result is either the ordinary authentication observer's win or one same token, raw request, decoded verifier result and pre-build Server whose successful builder records satisfy the existing `At` receipt. The actual accept of that raw request precedes that build in the public journal.

On the receipt branch, `Projected` supplies all unsigned/native equations. The verified key tuple equals the actual context's prekey, one-time and ML-KEM fields, or the existing joint-use Phase1 field-substitution event holds. Only this final verification-interface consumer uses the already approved full arbitrary-buffer attached-verification adapter. Its inherited narrow `ReadWritable` premise applies to the actual matching inner frame, as in the accepted-record receipt.

The proof does not discharge field substitution with a signing-history or EUF reduction. It does not assert that the successful build preceded Beacon acceptance merely from final journal membership. Root equality, registration-origin attribution, the complete eleven-field event and a probability bound remain separate consumers. Raw outer response bytes and signature buffers are not required to be unique.

## Validation and accounting

All nine public statements have exact standard-axiom guards. Focused direct checks compile the complete module against the existing private dependency prefix. The source programs, optional failures, real cache effects, and source query bounds are unchanged; this package adds functional receipt consumers and no oracle calls or security loss. This is not an implementation proof for Ed25519, X25519, ML-KEM, serialization, or a runtime bound.

The dependency is the published target-identity package `2c34d6aa027339349715afc362f3c3e123cf2f6c`. The new source is [PqxdhServerAuthPhase1Projection.lean](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhServerAuthPhase1Projection.lean).
