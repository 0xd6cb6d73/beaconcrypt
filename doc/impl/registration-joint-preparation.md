# Native registration preparation through indexed private services

`PqxdhRegistrationJointPreparation` proves that the actual Beacon registration preparation can use the existing private identity and KEM services while preserving the complete evaluated result. The client retains the source prekey and one-time scalars, public identity and KEM material, and the two private service indices. It carries no additional identity-seed or KEM-secret argument. This representation does not assert that retained values have independent or unequal bytes.

The compiler runs the original abstract response decoder and field projections, real public-key conversion, local scalar DH, assigned-ID projection and shared-secret erasure callback. It forwards the KEM decapsulation to the exact selected private KEM index and converted-identity DH to the exact selected joint Ed25519/X25519 identity index. Every optional rejection remains possible. The source order is unchanged: after the response fields and conversions, decapsulation precedes the four DH calculations, including the identity service calculation, and then the assigned-ID projection. The original extracted admission code consumes exactly the resulting input.

The comparison uses a private mathematical annotation of the original source callback. This annotation records the actual optional KEM and joint-DH replies in the existing histories. It does not change admission, query replies or the source's secret arguments. `annotated_query_erase` and `annotated_program_erase` prove that dropping this analysis state recovers the original callback and every adaptive source program. This is neither a new primitive oracle nor an assumption about an adversary's view.

The two local representation premises identify exact private slots: the identity pool contains the owner's seed at `identityIndex`, and the KEM pool contains the owner's complete key pair at `kemIndex`. They do not assert an honest network candidate, authentication, distinct public keys, or equality between a public owner address and either private index. The existing creation result establishes these relations for newly allocated private slots. Their preservation through the complete native scheduler, including live-field erasure and reveals, remains a consuming obligation; this module does not assume that global invariant as a protocol security conclusion.

| Statement | Established fact |
| --- | --- |
| `decapsulate_source` | The indexed KEM service and annotated original callback have the same optional reply and complete private pool under the exact KEM slot relation. |
| `dh_identity_source` | The same equality holds for converted-identity DH under the exact seed slot relation, using the existing joint primitive service. |
| `interpreted_evaluated` | The direct evaluated callback expression equals the executable service compiler on every request and private state, including missing indices. |
| `collect_source` | The actual optional source collector and compiled collector agree on the complete input and both complete private pools. |
| `annotated_query_erase`, `annotated_program_erase` | Removing only private analysis histories recovers the literal source callback and arbitrary adaptive program. |
| `prepare_source`, `prepare_continuation` | The original extracted admission and erasure follow the same collector result, including arbitrary continuations on the prepared result and entire private poststate. |
| `prepare_original` | Projecting the compiled preparation back to the source result gives the original source preparation distribution. |
| `annotated_query_slots`, `annotated_program_slots` | Annotation preserves all existing private seed and KEM slots on every supported outcome; only histories grow. |

`PqxdhRegistrationJointPreparationCosts` proves a separate query ledger for this exact operation. The optional source collector has at most one decapsulation callback, one identity-DH callback, and a conservative allowance of twelve other callbacks. Preparation increases that last conservative allowance to thirteen. These local allowances are upper bounds, not claims that all callbacks occur or exact counts of deterministic work. The executable service compiler emits at most one KEM decapsulation request, one joint static-DH request, and zero requests to every other service capability. Failed attempts count. Creation, signatures, reveals and local coin requests are absent from this compiler, not forbidden globally.

| Statement | Established bound |
| --- | --- |
| `collect_classes`, `prepare_classes` | The source callback partition has caps `1/1/12` and `1/1/13`, respectively, on every typed reply path. |
| `source_step_uniform`, `annotated_step_uniform` | Each actual callback pays its complete declared KEM direct and interpreted base-oracle randomness; annotation preserves that bill. |
| `uniform_bill`, `annotated_prepare_uniform` | The finite weighted partition sums to one complete `decapsCost` allowance for the whole annotated preparation. |
| `prepare_uniform` | The indexed client pays at most `decapsUniform + baseUniform * decapsBase` uniform queries under its exact private-slot relations. |
| `compiler_step`, `compiler_other_free`, `compiler_prepare_classes` | The executable compiler's only possible service requests are the one decapsulation and one identity DH; all other service query counts are zero. |

The uniform bill uses the existing `KemBound` contract for actual KEM and base-oracle programs. Joint DH is the already modeled deterministic functional interface, so it contributes one logical service request and no uniform query here. Local decoding, conversion and scalar DH remain actual local computations. Neither this ledger nor the zero count for other service queries declares CPU work or opaque ambient work free.

These 21 statements add no primitive security assumption, do not prove serialization internals, and do not state a secrecy or authentication advantage. The native owner/finish product-state routing, ownership through the full lifecycle, reveal/freshness rules, adaptive identity and session selection, global resource ledger and symbolic event consumer still have to use these local equalities. Existing one-session results and earlier `noCreate`/`noSign` scopes are unchanged. Private annotation slot preservation is not a snapshot, restoration or physical-erasure claim.
