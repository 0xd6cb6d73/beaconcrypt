# Accepted observations in the complete native R1 experiment

This package closes the outer source-game composition for the observation interface from `server-authentication-observed-schedule.md`. It proves the partition on the original game, transports the entire accepted observation to production constructor order, and supplies the query ledger for the exact constructed reductions. It adds no primitive assumption, successful-publication premise, event-transfer premise or selected-honest-session restriction. The remaining uniform observed event must still be bounded by its concrete component reduction before a publication-authentication result follows.

## The actual journaled source game

`PqxdhServerAuthObservedGame.body` and `game` execute the original source body and Extract-family interpreter with the unchanged adversary returning its chronological public query/reply journal. `body_erase` and `game_erase` recover the complete original programs by removing just that added journal. The private native state, family cache, histories, continuation and source sampler remain present. `reachable` obtains the original invariant and accept-attempt session bound from this exact erasure.

`Accepted observer` means the original execution has an actual acceptance annotation and the observer returns true on the root-erased ghost and public journal. `Owned` adds the already-defined accepted-owner gate for one index in `Fin (Q + 1)`. `accepted_cases` proves, on every actually supported run, that an accepted observation implies the original Extract-input disclosure event, the original distinct-Server collision event, or an owner coordinate. `accepted_probability` applies the finite union bound. Only the two charged bad branches discard the observer condition, and their probabilities are exactly those of the original game by journal erasure. No caller supplies a security-event partition.

`observed_flat` proves equality of the complete observed source and real-service skeleton distributions. It retains the whole journal jointly with the observed source ghost, using the existing complete-state interpreter relation. Its generic `Observation` may inspect the actual source ghost and sampled seed/scalar because it is used only for exact mathematical source correspondence. This is distinct from the later primitive reduction's `Observer`, which takes only the root-erased ghost and public journal. The more general mathematical projection is never substituted into that primitive interface.

## Constructed losses and exact owner accounting

The six statements in `PqxdhServerAuthObservedPartition` join that partition to the new observation-dependent schedule reductions. `owner_source` identifies each original owner event with its precise schedule source endpoint. `accepted_decomposition` and `accepted_decomposition_real` give the partition in nonnegative extended and ordinary real probabilities, discharging finiteness of the entire sum. `owner_uniform` applies the new schedule comparison, and `accepted_bound` concludes:

```text
Pr[actual accepted observation]
  ≤ Adv[joint Gap-DH, original scanClient extractor]
    + choose(Q, 2) · 64 / 2^256
    + sum over j : Fin(Q+1) of
        (Pr[uniform selected schedule, same observation]
         + L_observer(j)).
```

The disclosure extractor has coefficient one. `Q` counts all source accept attempts, including rejections. There is no additional raw-attempt or session-guessing multiplier in this partition. Each `L_observer(j)` is the sum of five advantages of reductions newly constructed from that same observer: root HMAC expansion, initializer Extract on the actual uniform32 sampler, initializer HMAC expansion, step Extract on the actual uniform32 sampler, and the two-block step HMAC expansion. The earlier seal-origin distinguishers' advantages are not reused for the changed event. The correlated 108-byte selected schedule and all real public HKDF evaluations are retained exactly as in the preceding package.

`observed_bills` proves the `ObservedBills` record for exactly this extractor and these new schedule reductions. Let `G`, `E` and `D` be the complete interpreted key-generation, encapsulation and decapsulation uniform costs from `KemCaps`, including each base-call allowance. The common context-plus-observer bound is `U = 256 + qCoin + 160Q + 64(qHash + qH) + G + QE + D`. The Gap-DH extractor has signing cap zero, decision cap `2qH(Q+1) + 2(Q+1)(qH+Q+1) + qH`, and uniform cap `U - 64`; its whole challenger game has cap `U`, including the two 32-byte challenge draws. The signing count is for the joint challenger's signing interface; locally known Beacon signing operations remain actual deterministic source operations.

The three HMAC reductions have challenge-call caps `1`, `1`, and `2`, and reduction-uniform caps `U`, `U`, and `32+U`. The real/random whole-game uniform caps are:

| Component | Real game | Random game |
| --- | --- | --- |
| Root HMAC expansion | `64+U` | `64+U` |
| Initializer Extract | `32+U` | `96+U` |
| Initializer HMAC expansion | `64+U` | `64+U` |
| Step Extract | `64+U` | `128+U` |
| Step HMAC expansion | `96+U` | `160+U` |

These are interface query counts, with explicit source KEM and base costs. Deterministic public primitive evaluation, journal processing and predicate computation are not asserted to take zero runtime. The final concrete observer must retain its own computational interpretation; this general theorem does not turn an arbitrary mathematical observer into an efficient algorithm.

## Complete native execution and source order

The five statements in `PqxdhServerAuthObservedExecution` apply the bound to the actual native handler. `native_flat` consumes the source invariant from the real context sampler, then the complete native interpreter relation and full journal coupling. `native_order` applies the existing constructor interchange to the entire evaluated Phase-1 and native continuation: Server seed, Beacon seed, Beacon prekey, KEM generation, then the Phase-1 one-time scalar. It does not infer a continuation law from equal marginal key distributions. `ordered_observed` joins those equalities to the original source game.

`acceptedObservation` ignores the generic projection's seed/scalar arguments and tests only actual acceptance plus the supplied root-erased observation. `ordered_accepted_source` identifies this unrestricted native accepted event with the original event that was partitioned. `ordered_bound_with_resources` combines the same displayed inequality and `ObservedBills` for that production-order native execution. The original BadB/CollB gates occur only in the finite decomposition, not as premises of the headline event.

The inherited R1 contracts remain the explicitly documented restricted programmable zero-salt Extract random oracle on 192-byte inputs, joint twist-inclusive Gap-DH interface, X25519 class and scalar-spread laws, and full source Extract/Expand wiring. The theorem names ordinary constructed Extract and HMAC game advantages and does not assume their desired protocol conclusion. Its cryptographic bound uses the no-seed-reveal experiment; the structural correspondence itself also covers the exposed-seed experiment. There is no KCI claim, later assigned-ID agreement, persistence or snapshot claim.

## Remaining consumer

A concrete publication observer still needs its exact source occurrence interpretation and a bound on each uniform endpoint. A successful outer writer must be related to the actual build occurrence, rather than inferred from an unconstrained decoder or assumed writer injectivity. Inner successful encryption followed by writer failure remains possible and is handled by the separate withheld-output proof. Nothing here establishes a random-tag law conditioned on such failure, excludes known-key aliases, removes private component histories, or proves full replicated-session authentication. Central imports, inventory and the full validation matrix belong to the reviewed consuming integration; these 17 statements have focused Lean and standard-axiom checks.
