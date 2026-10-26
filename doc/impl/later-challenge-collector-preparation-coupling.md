# Complete collector and preparation coupling for later challenges

This checkpoint extends the [complete prefix coupling](later-challenge-full-prefix-coupling.md) through the literal prepared collector and independently couples the actual generated preparation. It proves operational distribution relations for the same source programs. It does not yet prove later-record confidentiality or equate the adversary decisions after admission.

## The complete collector

`PqxdhLaterChallengeCollectorCoupling` has eleven guarded results. `unrestore_restore` and `restore_unrestore` prove that splitting the native product into its complete local state and ROM cache is invertible for both pending and completed cuts. `collect_post` proves that the original input's outside Post field is unused by the collector: the real continuation is already in the cut descriptor. `run_split` factors the complete original prepared run into its exact prefix and this unchanged collector.

`step_pending` proves that a pending collected result preserves the literal incoming descriptor, local state and reached cache. `step_missing` proves its exact pure return when that address is absent. `step_cached` proves that a present-address execution returns its actual Boolean decision and cache, rather than fabricating a pending descriptor. These are consequences of the original collector and its actual interpreted support, not a callback success premise.

`step_late` keeps completed and post-admission cuts in the explicit residual relation. `step_same_address` proves that paired early cuts inspect the same real cache entry, using their equal address and full local/cache state. A missing entry retains the paired pending descriptors; a cached entry uses a product coupling of the two actual completed distributions. `step_coupled` applies this reasoning to every alternative of the checked full prefix relation, including the initial Builder, a before-admission wrapper callback, and both complete/inside/used outcomes. `prepared` composes the actual prefix coupling and collector coupling by relational bind.

The relation includes both original probability marginals. Its residual alternative does not say that individual cached or completed decisions agree, that refusal probability vanishes, or that those outcomes may be ignored in a secrecy bound. Complete collector decisions have the state representation returned by the original API; pending branches additionally retain their original source state and callback. No new state erasure is imposed by the relation.

## Actual generated preparation

`PqxdhLaterChallengePreparationCoupling` has four guarded results. The original preparation depends on its outside Post on common completed paths. Consequently, it is incorrect to assume that the entire prepared packet is sampled identically for both challenge bits.

`completed_map` instead retains arbitrary complete decision/cache distributions in an explicit completed relation. `dispatch` couples the literal accepted/changed/rejected/ineligible admission code for arbitrary Posts. All pre-admission decisions and draws are shared; an eligible pending outcome retains the same complete generated output and reached ROM cache. The DH failure branch still performs its original encapsulation before executing the real completed continuation. Common paths keep each world's original decision and hash effects.

`run` executes the unchanged generated identity, prekey, one-time and selector prefix before applying that dispatch relation. `prepare` includes the original KEM key generation before the source prefix and outer encapsulation afterward, in their original full continuation order. It yields either identical complete private packets and reached caches, or two retained completed packets. The KEM secret remains in this internal interpreter packet and is not a protocol reply. There is no premise that the selected candidate is honest, nor a new security assumption on common-path behavior.

## Stored source input

`PqxdhLaterChallengeGeneratedCoupling` has three guarded results. `prepared_post` proves that replacing the original unused Post before installing the explicit challenge wrapper has no effect on the prepared sampler. `prepared_map` identifies the actual evaluated carrier as the exact deterministic representation of the original collector output plus the source input stored by the existing sampler, with the same reached cache. `prepared` transports the complete collector coupling through this map; each world keeps its own original wrapper inside the stored source input.

The source input, selected continuation, initial expansion and private KEM packet remain literal parameters. This checkpoint does not yet bind the two newly proved preparation and prepared-carrier relations into `PqxdhLaterChallengeSampler.run` or couple its subsequent parent/nonce/chain draws. That join is the next consumer, rather than an assumed generator interchange.

## Assumptions, accounting and remaining composition

All eighteen statements use only the existing source program definitions, arbitrary actual callback interpreters and the standard Lean axioms. There is no primitive implementation proof, new cryptographic assumption, security conclusion hidden in a callback premise, or added target-honesty premise. The source calls are unchanged; representation maps and relational proofs add no protocol or oracle calls. The already established `PreparedCapture.run_budget` and `Sampler.run_budget` transport the original complete source bills. This is not a numeric budget for the unfinished global secrecy reduction, and arbitrary callbacks and common-path work retain their original costs.

The remaining consumer must join the actual generated packet and its selected adversary, all original material draws, the same-source before/inside/used chronology, and the nonce-stopped resume comparison. Alias exclusions, nonce-refusal probability, freshness, source compiler correspondence, global target/session/record selection and raw-receive reduction losses remain explicit obligations. None can be removed using the current residual relation or support-only facts. The native selected record still requires `number.val = depth + 2` in the separate source-event exclusion theorems.

Direct module checks cover eighteen guarded public statements: two representation inverses require no axioms; the other sixteen report only `propext`, `Classical.choice` and `Quot.sound`. No Rust or primitive implementation changed. Full repository integration, inventory refresh and final verification remain the integrating branch's responsibilities.
