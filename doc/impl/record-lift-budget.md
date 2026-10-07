# Record-lift open-program resource transport

`PqxdhRecordLiftBudget.lean` proves resource composition for the frozen `PqxdhRecordLiftInterface.program`, including the joint record-request refinement requested by Claude's answer 56. The actual program runs through startup, the existing secrecy wrapper, native command dispatch and the stateful environment handler. Its thirteen statements introduce no cryptographic premise or new contract. The effect bound uses the existing `Frame` and outer `Budget.Respects`; the joint send/raw bound needs only `Budget.Respects`, because the restricted environment and startup types cannot issue record requests. Interpreting those requests, installing hidden seeds and answering shared primitives still requires the separate world accounting.

## Restricted-effect requests

`WorldEffect kind` counts requests in the restricted-effect summand of `WorldSpec`. That summand carries direct public coin and hash requests as well as effects emitted by the environment. Its three classes are uniform-oracle calls, BLAKE2b capability calls and administrative capability calls. This predicate excludes the initial constructor handoff and the four ordinary-record requests. Excluding those abstract requests does not make their interpretation free: `program_bound` does not count work performed by a later interpreter inside them.

Write `B = caps.outer`, `L = bounds.max` and `E(kind) = caps.envTotal allowance kind`. `program_bound` supplies the following upper bounds on every execution path of the actual open program, in either observation mode.

| Request class | Upper bound |
| --- | --- |
| Uniform-oracle calls | `startupCoins + B.coin + B.test + L * B.fresh + E(.coin)` |
| BLAKE2b capability calls | `B.hash + E(.hash)` |
| Administrative capability calls | `E(.administrative)` |

These are bounds, not assertions that every permitted call occurs. Rejected test or fresh commands can do less work, and the shared test bit need not be sampled on every test. The existing secrecy-wrapper theorem conservatively charges at most one coin per test and at most `L` byte draws per fresh attempt. No success assumption is needed. Startup is charged even when it returns no constructor and the program stops. A successful startup passes through the actual constructor handoff before entering the wrapped adversary.

`E(kind)` is the existing finite sum over `Fin 14` of `B.cap class * allowance class kind`. Only classes 1 through 6 invoke the environment: create, bundle, accept, build, finish and HMAC. `nativeCost` uses the given allowance for those six classes, charges one direct coin at class 0 or one direct hash at class 7, and charges no restricted effect for an abstract record request. `cost_sum` proves that composing this twelve-class native matrix with the existing fourteen-class secrecy-wrapper matrix fits `directCost + E`. It counts environment calls against their original command caps; extra record sends or coin draws inserted by test and fresh do not multiply an environment allowance. Allowances in unused classes may be nonzero, because the resulting finite sum is still an upper bound. For CE's planned allowance of one hash at build and finish and zero elsewhere, `E(.hash)` reduces to `B.build + B.finish`; proving that allowance for the erased CE environment remains CE's obligation.

`environment_bound` transports the actual per-command `Frame` allowance through the effect embedding. `native_bound` checks every native branch, and `wrapped_bound` composes that handler with the existing secrecy-wrapper cost matrix using finite weighted query accounting. `startup_bound` proves the startup coin bound and zero hash/administrative effects. `program_bound` composes the actual optional startup, constructor handoff and arbitrary adaptive continuation. The environment state, slot count, payloads, responses and observation mode remain arbitrary.

## Joint record-request bound

Adding the existing separate wrapper caps for Server sends and Beacon sends charges each test or fresh request twice, since either role could be selected. That per-class matrix alone yields `B.sends + B.test + B.fresh` for sends. The new `RecordKind.send` groups native classes 8 and 10 into one predicate. `recordCost .send` charges one at full-interface classes 8, 10, 12 and 13, and zero elsewhere. `RecordKind.raw` similarly groups native classes 9 and 11, with cost one only at full classes 9 and 11. `wrap_record_step` inspects the actual secrecy handler: an admitted test or fresh performs at most one joint send after its zero-record coin work; a rejected request performs none. Neither secrecy command performs a raw receive.

`wrap_record_bound` composes this joint step bound with the existing mode projection and finite client budget. Its arithmetic gives exactly the existing `Budget.sends` and `Budget.receives`, without the extra `B.test + B.fresh`. `WorldRecord kind` counts the corresponding request kind across both roles in the world's record summand. `environment_record_bound` and `startup_record_bound` prove zero such requests from the restricted environment and startup, without a resource or correctness premise. `native_record_step` establishes the actual one-or-zero dispatch cost, and `native_record_bound` preserves a client's joint cap through arbitrary interleaved environment work. Finally, `program_record_bound` includes optional startup and the constructor handoff and proves the following caps for the actual open program in either mode.

| Joint record class | Upper bound |
| --- | --- |
| Server or Beacon send | `B.sends = B.serverSend + B.beaconSend + B.test + B.fresh` |
| Server or Beacon raw receive | `B.receives = B.serverRaw + B.beaconRaw` |

Every API attempt remains eligible for the bound, including missing handles, parser rejection and later operation failure; no accepted-record premise occurs. These are counts of requests passed to the interpreter. The source step bounds of one derivation per send and at most 51 per raw receive still need to be composed through the actual world before concluding `Caps.derivations = B.sends + 51 * B.receives`. The joint request theorem removes the double-count obstacle identified in answer 56; it does not silently supply that world theorem.

## Assumptions and remaining interpreter costs

The cryptographic contract list is empty for all thirteen theorems. The restricted-effect results use the existing resource predicates `Frame` and `Budget.Respects` where applicable. The joint results use the explicit client query bound or `Budget.Respects` where applicable, and their zero-record helpers rely only on the interface types. None assumes a codec law, source correspondence, freshness, nonce uniqueness or hidden installation correctness. Every declaration has an exact axiom guard allowing only `propext`, `Classical.choice` and `Quot.sound`.

The world's native primitive work must still be accounted for separately, including both directions, test and fresh sends, every raw receive attempt and derivation limits. The environment's explicit hash and coin effects are already counted here, but shared-hash cache misses and their actual uniform draws belong to the primitive interpreter. Lazy hidden-seed draws on installation likewise belong to the world, even though the administrative installation request itself is counted here. Startup's private constructor handoff is outside both predicates; any work in its interpreter requires its own proof. No ambient oracle work is silently included in these bounds.

The `caps.sharedHash` field is not a hypothesis or a conclusion of this component. Relating it to `B.hash + B.sends + B.receives + E(.hash)` now has the required joint send bound, but still requires the ordinary-record interpreter's per-request hash bound and CE's allowance instantiation. The module proves no installation schedule invariant, source-game equality, failed-registration erasure or computational security result. It changes no frozen interface, production Rust, wire format or binding.

## Validation and publication status

All thirteen statements passed independent semantic review: the original six effect statements also received Claude's C4 approval in answer 56, and the seven joint record statements resolve the send-count refinement requested there. The final source is reconciled against integrated LQ-F central `dd1efd6fc48eae94009bea201861501f2c94d8a0`. Its module and root-import checks passed through `coord.sh lean codex`, using `timeout 180`, Lean 4.34.0 `-j1 -M8000` and a fresh private dependency mirror. The Nix-backed inventory check and transcript-fidelity target also passed; the latter ran 20 Python tests and 30 Rust tests with an owned Cargo target and two jobs. The publication receipt records exact source, metadata, artifact, log and dependency-path hashes. Final metadata review is approved, and Claude's answer 69 approves the joint record refinement without changes while keeping the world-interpreter bounds as the next obligation. No full build, ProVerif run or complete production mutation suite is claimed; no Rust source changed.
