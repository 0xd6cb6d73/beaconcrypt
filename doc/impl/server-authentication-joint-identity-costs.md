# Complete resources for the actual R1 joint-identity reduction

This guide closes the uniform and logical static-DH ledger left open by [the concrete source weak-EUF reduction](server-authentication-joint-identity-euf.md). `PqxdhServerAuthJointIdentityUniformCosts.source_bound_with_resources` combines the existing coefficient-one source substitution bound with resource statements about that same executable reduction and its ordinary joint Ed25519/X25519 challenger. The reduction and source experiment are unchanged. This is a resource completion for one R1 target Beacon identity and one actual three-message Phase1 bundle; the eleven-field session consumer and the replicated computational/symbolic experiment remain separate work.

## Exact interface and costs

Let `q` bound every original adaptive API call on every input and reply path, including uniform queries, accepts, builds, finishes, public HMAC and hash queries, and installed-kernel reveals. Let `qFinish` separately bound every attempted finish, including inactive calls and rejection. These are syntactic source query caps, not assumptions that the attacker chooses an honest candidate, makes a successful request, or supplies a fresh ciphertext.

The existing `KemCaps` and `KemBound` expose the complete primitive programs' direct uniform and base-interface counts. If `B` bounds uniform work of each base callback, write `G = gU + B*gB`, `E = eU + B*eB`, and `D = dU + B*dB` for key generation, arbitrary-public-key encapsulation, and optional decapsulation respectively. All permitted replies and failing primitive results remain in those programs. The original source-cost proofs interpret every base callback, so its work contributes to these quantities.

| Executed interface | Uniform-query allowance |
| --- | --- |
| One public uniform call | 1 |
| Server accept | `96 + E` |
| Server response build | 64 |
| Public HMAC call | 64 |
| Public CTX/BLAKE2b hash call | 64 |
| Beacon finish | `D + 128` |
| Installed-kernel reveal | 0 |
| Common conservative per-call allowance | `128 + E + D` |
| Concrete weak-EUF reduction | `96 + G + q*(128 + E + D)` |
| Ordinary joint challenger plus reduction | `128 + G + q*(128 + E + D)` |

The common allowance intentionally pays both optional KEM costs for each source call. It bounds the actual operations above without requiring a more restrictive schedule. The local constant 96 is the actual Server identity seed, prekey scalar, and one-time scalar, each sampled with 32 byte draws. The target Beacon identity's 32 draws belong to the challenger and are added only in the whole-game line. Generation order remains the checked source order, and the existing whole-continuation seed interchange is unchanged.

The same reduction has signing cap 3 and logical joint static-DH cap `qFinish`. The original Beacon preparation also has logical decapsulation cap one per attempted finish, independently of whether it succeeds. `qFinish` is deliberately conservative for the one-shot Beacon lifecycle. No additional signing, candidate-key, signature-field or attempt-selection factor is introduced. The public extractor still scans at most three detached fields per original journal entry.

These are oracle-query bounds. The 32- and 64-query internal samplers here draw bytes; an arbitrary public uniform request counts as one request to its original finite-uniform interface. This does not claim bounded CPU time or byte length for arbitrary messages, abstract decoding, local signature verification, deterministic primitive evaluation, or a large finite-uniform request. KEM base-oracle work is explicitly interpreted and charged, rather than being treated as cost-free ambient work.

## Native state and shared caches

The accounting covers the original native programs, preserving their optional replies, failure branches, caches, logs, token allocation and consumption, complete private state, initializer and raw receive continuation. A restricted 192-byte zero-salt Extract table miss uses 64 draws, while a hit adds none. Expansion remains the original real HMAC function. An arbitrary public HMAC call outside the approved restricted Extract slice stays real; inside the slice it shares the same Extract cache. The source is never replaced by an independent public-HKDF table.

The native Server accept pays 32 scalar draws, full arbitrary-key encapsulation, and up to 64 Extract draws. A native response build pays at most 64 draws for the shared CTX hash cache. A Beacon finish pays its actual optional decapsulation, up to 64 Extract draws, and up to 64 CTX cache draws. Its complete after-root initializer, application parsing, cached/future receive path and failure behavior remain executed. Repeated real KDF evaluations are not replaced by fresh samples. Optional inner or outer writer refusal remains in the original computation.

The joint challenger supplies only the target identity signatures and target converted-static-DH replies. The target seed never becomes an executable reduction parameter. Every locally generated key and every nontarget operation remains available at its actual source position. Stand-alone EUF-CMA is not used to simulate related Ed25519/X25519 operations.

## Checked statements

`PqxdhServerAuthJointIdentityDhBudget` contains fourteen statements:

| Statement | Plain-English content |
| --- | --- |
| `coins_no_dh` | Fully executed local randomness makes no target static-DH request. |
| `collect_identity` | The original all-reply Beacon collection makes at most one identity-DH callback. |
| `prepare_identity` | Core admission and erasure add no identity-DH request. |
| `auxiliary_dh` | The actual auxiliary interpreter forwards exactly the identity-DH query class. |
| `prefix_dh` | Selected-prekey routing preserves that class and its cap. |
| `prepare_dh` | Complete preparation has joint static-DH cap one. |
| `stage_dh` | The full root/record continuation adds no joint static-DH request. |
| `finish_dh` | Every active, inactive or failed finish has cap one. |
| `handler_dh` | Only attempted finish calls need a joint-DH allowance. |
| `program_dh` | The complete adaptive API consumes at most `qFinish` joint-DH queries. |
| `phase1_no_dh` | Actual Phase1 publication uses signatures but no joint static DH. |
| `execution_dh` | Phase1 plus the full adaptive continuation retains `qFinish`. |
| `capture_dh` | Source generation and literal public journaling retain `qFinish`. |
| `reduction_dh` | The concrete forgery extractor retains the captured execution's cap. |

`PqxdhServerAuthNativeUniformCosts` contains sixteen statements:

| Statement | Plain-English content |
| --- | --- |
| `extract_table_uniform` | The actual Extract cache needs at most 64 draws for a query. |
| `root_bytes_uniform` | The complete root operation, including real expansion and history, retains 64. |
| `beacon_root_uniform` | Native Beacon root instrumentation retains 64. |
| `after_root_uniform` | The complete original continuation after a root needs at most 64 draws. |
| `simulate_native_ctx` | Lifting the full CTX computation commutes exactly with its native-state interpreter. |
| `ctx_uniform` | That lift preserves an arbitrary whole-computation uniform cap. |
| `beacon_tail_uniform` | Original root plus complete after-root tail needs at most 128 draws. |
| `logged_root_uniform` | The actual Server root and session touch retain 64. |
| `client_uniform` | Core accept, root and consumption preserve the Server root allowance. |
| `prefix_uniform` | The literal Server prefix costs `32 + E`, including all encapsulation work. |
| `accept_uniform` | Allocation, complete prefix/root execution and pending publication cost `96 + E`. |
| `native_build_uniform` | The whole original response builder costs at most 64, including failed writers. |
| `hash_uniform` | The original shared hash-cache query costs at most 64. |
| `hmac_family_uniform` | Real public HMAC and the restricted shared Extract slice cost at most 64. |
| `hmac_uniform` | Original native HMAC instrumentation preserves that allowance. |
| `coin_uniform` | An original public uniform callback costs one query. |

`PqxdhServerAuthJointIdentityUniformCosts` contains eighteen statements:

| Statement | Plain-English content |
| --- | --- |
| `coins_uniform` | Full local primitive computations retain their uniform bill on the joint interface. |
| `collect_decaps` | Original all-reply Beacon collection makes at most one logical decapsulation. |
| `prepare_decaps` | Core admission and mandatory erasure add no decapsulation. |
| `prepare_classes` | Decapsulation and all other callbacks form an exhaustive bounded partition. |
| `auxiliary_uniform` | Only optional KEM work in the auxiliary interpreter adds uniform queries, with all base work charged. |
| `prefix_uniform` | Selected-prekey routing retains that exact per-class bill. |
| `prepare_uniform` | The weighted callback partition bounds full preparation by `D`. |
| `stage_uniform` | Preparation and the entire native tail cost at most `D + 128`. |
| `finish_uniform` | Every attempted original finish preserves that allowance. |
| `handler_uniform` | Every original API query is covered by `128 + E + D`. |
| `program_uniform` | All `q` adaptive calls cost at most `q*(128 + E + D)`, retaining the full returned state. |
| `phase1_uniform` | The literal generated three-signature publication adds no uniform query, including writer refusal. |
| `execution_uniform` | Phase1 followed by the entire adaptive native run preserves the all-call allowance. |
| `capture_uniform` | The concrete captured execution adds the actual local `96 + G` generation cost. |
| `reduction_uniform` | Public extraction preserves that complete execution bill. |
| `game_uniform` | The ordinary joint challenger adds its own 32 target seed draws. |
| `expanded_game_cost` | The whole-game formula explicitly expands every direct/base KEM term. |
| `source_bound_with_resources` | The original coefficient-one source event bound and all three joint-interface caps hold for the same concrete reduction. |

## Assumptions, validation and integration

No new security assumption is introduced. `KemBound` supplies ordinary syntactic resource contracts on existing primitive programs; it does not assert a protocol conclusion. The source substitution inequality reuses the published ordinary joint-use weak-EUF reduction. The R1 execution still uses the approved restricted Extract programmable ROM and shared programmable classical CTX/BLAKE2b ROM. The existing full attached-verification adapter is needed when a later source receipt consumer translates arbitrary attached signatures; this resource theorem does not replace it with a well-formed-only law. There is no honest-target-candidate premise.

The final checkpoint is checked module by module with Lean 4.34, with an exact guarded axiom statement for each of the 48 public theorems and a forbidden-placeholder/custom-axiom scan. No Rust, ProVerif, primitive implementation, serialization implementation, persistence or snapshot code changes are part of this checkpoint, so no Rust mutation run is required. Aggregate build, root imports, generated trust inventory and the final full verification matrix are integration obligations; these focused checks do not claim that matrix has already run on this topic.

The source event still concerns one original R1 bundle and all its adaptive accept attempts. It cannot silently cover additional honestly signed bundles under a reused identity. The completed resource statement does not establish the eleven-field registration correspondence, arbitrary replicated sessions, or the common computational/symbolic transfer. Those consumers must use the same execution, source provenance, freshness rules and capabilities when composing this reduction.
