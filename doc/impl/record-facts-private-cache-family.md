# Private suffix-cache families

`PqxdhRecordFactsPrivateCacheFamily.keyed_observation` lifts the [replay/random per-key discard law](record-facts-private-cache-random.md) to an adaptively chosen family of material coordinates sharing one public ROM. It compares the `uncountedKeyed` endpoint with `erasedKeyed` from any initial `CtxPrivate` state. The whole returned result, every retained local history, and the complete base state have the same contextual probability law after the private suffix dictionaries are omitted. Every coordinate's mode must be replay or random; real AEAD opening is explicitly excluded.

## Exact family and state

`FamilyRO` is the ordinary lazy digest oracle on `(material coordinate, suffix)`. This indexing keeps the per-coordinate private dictionaries distinct even when two coordinates happen to have equal key bytes. `familyLens` reads and updates only those dictionaries. `observeFamily` retains `state.base` and every coordinate's `AdaptiveCtxSharedHash.Local`: successful seals, used nonces, public/private input logs and raw-attempt count.

`localLens` focuses one full key entry together with the shared public ROM. Updating it changes that entry and the shared ROM, while preserving all other keys and every other base field. `uncountedKeyed` runs the actual existing linked `keyImpl` at the key selected by the current `materialAt state.base.chain label`, through this lens. `uncountedKeyed_run` gives its literal state update. Only the outer `sampled` uniform-counter instrumentation of `PqxdhRecordLiftIdeal.keyed` is omitted in this definition; a separate counter-erasure simulation is needed to connect them. No equality of their uniform counters is claimed here.

## Completion and adaptivity

`complete_local` identifies a family completion at `(label, suffix)` with completing that exact local suffix at `label`. `localLift_other_commutes` proves that a step at another coordinate cannot inspect or alter this dictionary, while preserving shared hash effects. `localLift_commutes` combines that fact with the earlier same-coordinate lazy-cache commutation proof. Thus a completion can pass both a later same-coordinate seal and arbitrarily interleaved requests at other coordinates without replacing correlations by independent samples.

`baseRead_commutes` justifies choosing the key from retained base state. `completeOpt_local` and `factor_local` lift the per-key discarded lookup factor to the complete coordinate-family state. `localPointed_commutes` additionally preserves the deferred point itself. `pointedFromBase_run`, `factorFromBase`, `local_mode_factor` and `selected_factor` package the exact base-selected endpoint without any honest-key, freshness or statistical premise. `keyedPointed_commutes`, `keyedPointed_run` and `keyed_factor` put these pieces together for every keyed query. Finally, `keyed_observation` applies the checked lazy-oracle discard theorem to the entire adaptive `KeyedSpec` program. The final result is quantified over arbitrary subsequent probability-program observations of the retained result and state.

A raw request still increments its attempt count and records every parsed private-input suffix. It returns the same optional replay plaintext and retains parser rejection. A later seal still queries its genuine lazy dictionary. Coins and public hashing stay on their original linked endpoint. Only discarded raw private completions are postponed and omitted.

## Scope and costs

This is an operational family theorem, not yet a theorem over all `ServiceSpec` operations or the final record world. In its `KeyedSpec` program, the chain table supplied in the initial base state is not modified by keyed requests. Interleaved source allocation, evolving-key lookup, known-key operations and publication require the next service-level composition. The actual protocol's original uniform counter must first be related to the counterless endpoint; it is never silently preserved or declared free by this law.

The observed base includes all primitive effect counters and the shared public ROM as supplied to the uncounted family game; this game leaves its uniform counter unchanged. Original source/reduction uniform and private-query budgets remain required independently. The theorem supplies no collision, guessing, publication, origin or binding bound and requires no new primitive, codec or adversarial contract. Snapshot and persistence behavior are outside its scope.

Seventeen public statements have guarded `#print axioms` checks. Only `propext`, `Classical.choice` and `Quot.sound` occur. Direct module validation uses the published central `84a07b155d71574ae133d4db8b868f9a818b2c1a` dependency path and the reviewed two predecessor modules. Root imports, analysis and inventory updates remain integration work.
