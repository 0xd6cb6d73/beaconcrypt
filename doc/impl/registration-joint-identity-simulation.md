# Actual initialized registration in the ordinary joint-identity game

Status: the three proof modules and their 29 guarded statements pass focused Lean 4.34 checks and independent semantic review approved their operational simulation and counts. Central semantic integration and aggregate verification remain pending. This is an operational simulation and resource theorem. The accepted-signature report, freshness/selection reduction and computational authentication hop remain unfinished.

## The executable reduction

`PqxdhRegistrationJointIdentityCompiler.initialized` is a concrete client of the existing `PqxdhDynamicIdentityPool.DynamicSpec`: uniform randomness, dynamically generated Ed25519/X25519 identities, signing/converted-DH service requests, and explicit identity reveals. It first runs the actual Server constructor, including runtime initialization and the supplied-seed length check, then the existing fourteen-class adaptive registration command program. It starts with an empty KEM pool and empty source handle registry. Actual local KEM generation/decapsulation, all native callbacks and the runtime state stay inside this client with their existing implementations and random draws.

The ordinary joint identity endpoint is the already declared joint-use primitive interface. Its generated seed controls both Ed25519 signing and converted X25519 DH, with the stated rejection behavior. This work does not replace that contract with plain Ed25519 EUF-CMA and does not add a protocol authentication premise. It does not prove any primitive implementation.

## Source indices and known imports

`PqxdhRegistrationJointIdentityRouting.Registry` distinguishes a caller-known seed from a generated challenger index. Every successful source creation appends one registry entry. An imported Server therefore occupies a source index without occupying any generated challenger index. Subsequent Beacons receive their exact source allocation index, while private requests route to the separate challenger index. Public key byte equality is never used to choose the private owner, and no public-key injectivity premise appears.

`resolve_append` and `project_created` prove that appending a challenger seed preserves every earlier decoded owner and installs exactly the actual new seed. `create_run` retains the entire coupled challenger/registry state in the same source-order draw. `create_source` projects this run to the original complete source identity state. `initial_valid`, `created_valid` and `query_valid` establish that every generated handle resolves to an existing challenger seed throughout the actual execution. The default value in the total analysis function `resolve` is consequently unreachable for generated registry entries; it is never available to the executable client.

`query_source` covers identity creation, known-seed signing/DH, generated signing/DH, missing handles, actual reveals, explicit service coins, local ambient coins, and imports. The complete native-index observation history is retained. Ambient random draws belong to the ordinary challenger's full transcript but do not become native identity-service observations. `program_source` propagates the proved invariant through every supported complete adaptive continuation. It is equality of the full projected source execution, not equality of marginal key distributions, and it interchanges no generator.

## Complete initialized source correspondence

`PqxdhRegistrationJointIdentityCompiler.coins_complete`, `native_run` and `forward_run` show that local KEM/runtime work and forwarded identity requests retain all other state coordinates. `query_source` and `program_source` then reconstruct the original initialized service interpreter for every callback and entire adaptive program.

`reduction_source` combines that result with the source-index router. Its executable reduction has no generated identity-seed input: challenger seeds are used only by the final mathematical state projection after ordinary game interpretation. Caller-known imports and locally simulated KEM secret keys are legitimate local state of this identity reduction. `initialized_source` applies the construction to the actual initialized registration program and derives its equality to `PqxdhRegistrationJointInitializedSchedule.source`. The equality retains actual generated/imported origin, constructor rejection, optional command replies, all native fields, owner registry, private KEM material, native identity/KEM histories and runtime state. It needs no honest-target, acceptance-success or freshness premise.

## Query accounting

`PqxdhRegistrationJointIdentityCosts.route_step` and `route_program` retain every nonuniform capability bound through source-index routing, for all typed challenger replies and every registry. `coins_nonuniform` states only that local random work emits no private identity request; its uniform cost is retained separately. `compiler_step` and `compiler_program` propagate the original source-private bounds through the actual local KEM/runtime interpreter. `reduction_private` combines both transformations, and `initialized_private` supplies the concrete initialized scheduler's bounds.

For source budgets `qCreate`, `qBundle`, `qAccept`, `qFinish`, `qIdentityRead`, and `qKemRead`, the ordinary joint reduction has these upper bounds:

| External capability | Bound |
| --- | --- |
| Generated identity creation | `qCreate + (supplied Server seed is absent ? 1 : 0)` |
| Ed25519 signing | `3 * qBundle` |
| Converted static X25519 DH | `qAccept + qFinish` |
| Identity reveal | At most `qIdentityRead + qKemRead`, a conservative inherited live-read cap |

Missing owners, failed callbacks and rejected disclosures are included as attempted source requests. Known-seed operations add no external identity call. KEM services remain real local computations in this identity reduction; the ordinary identity interface has no KEM query constructor. The earlier separate KEM creation and logical-decapsulation caps remain `qCreate` and `qFinish`.

`initialized_uniform` preserves the complete evaluated real ordinary-game bill. With actual interpreted KEM costs `G`, `E`, `D` and initialization bound `qInit`, it is:

```text
qInit + (supplied Server seed is absent ? 32 : 0)
+ qCoin + (64 + G) qCreate + 32 qBundle
+ (96 + E) qAccept + 64 qBuild
+ 69 max(64, D) qFinish + 64 qHmac + 64 qHash.
```

This is a bound on the complete evaluated real challenger computation, including source/base randomness. It is not yet an all-reply uniform bound for a replaced challenge interpreter, and it does not supply the missing global logical Extract/HMAC/CTX query partition. No CPU-cost or zero-cost ambient-work claim follows.

## Remaining security and source scope

The next security consumer must report the exact publicly supplied attached signatures from each actual raw Server acceptance attempt, connect fresh accepted changed fields to the actual per-owner signing/reveal history, then apply the existing dynamic report stopping and target-selection reductions. Imported identities must remain excluded from generated-target selection. Reporting must keep the original raw candidate and actual verification result; it must not fabricate a target using recovered secret plaintext or seed material.

The experiment remains one initialized Server and arbitrarily many typed Beacon creations under the documented fourteen command classes. Raw constructor rejection, the compatibility `new_onetime_keypair` helper, deletion methods, full record scheduling and a general multi-Server dispatcher remain beyond this surface. The retained source experiment also still uses its explicitly identified restricted Extract idealization; this operational correspondence supplies no public-fixed-HKDF/random-table security claim. Full secret-input KDF integration, freshness, target selection, adversarial capabilities and adjacent global cryptographic hybrids remain separate obligations. Snapshot restoration and persistence are outside the requested proof scope.
