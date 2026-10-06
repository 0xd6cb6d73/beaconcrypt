# Open private services in the actual initialized registration program

The thirty-one guarded statements in `PqxdhRegistrationJointOpenBackend`, `PqxdhRegistrationJointOpenInitialization`, `PqxdhRegistrationJointOpenCosts` and `PqxdhRegistrationJointOpenInitializedCosts` factor the [actual initialized scheduler](registration-joint-initialized-schedule.md) into an executable client whose indexed identity/KEM requests remain open until the final interpreter supplies their replies. The client keeps the exact existing source constructor and command continuations. It never receives the private identity/KEM pools as an argument. Supplied Server seed material remains caller-known and distinct from generated identities.

This is a concrete operational factoring and accounting result. It does not replace a component by an ideal one, prove authentication from the names of primitives, or infer a security advantage from preserved key ownership. The original restricted Extract and CTX native interpretations are unchanged. In particular, no claim equates a public fixed HKDF with an independent random table; a production computational hop must retain real public evaluations and supply its own proved secret-input reduction.

## Complete open backend

`PqxdhRegistrationJointOpenBackend.native` runs the actual local native callback while forwarding all its uniform requests through the existing explicit ambient channel. The local state and every optional result stay intact. `pool` leaves actual indexed identity/KEM requests as oracle requests. `run` interprets those private services and reassociates the complete private/local state; it is the mathematical execution boundary, not a new primitive security assumption. `native_run`, `pool_run` and `run_bind` prove exact equality for those executions and arbitrary continuations.

`prefixImpl` interprets every real Server raw-collector auxiliary callback against the current consumed-registration list while leaving its indexed static-DH request open. `prefix_query` and `prefix_program` retain the entire collector and its complete callback order, replies and state. `prepare_run` reinstalls the exact optional collected inputs and consumed poststate beside the untouched native state. `accept` then runs the original session allocation, core acceptance, actual-input root callback, clearing, binding consumption and optional pending publication. `accept_run` connects this entire execution to the reviewed indexed Server accept, including every failed branch.

`impl` connects the actual bundle/finish/private-service backend and all existing shared callbacks to this open interface. It interprets local Beacon tails, Server build/publication, public HMAC/hash and current Server-kernel disclosure through their original native code. `query_run` and `program_run` prove equality with the complete previously checked seedless backend. `compile` consumes the actual public-command client, its encoded live owners and its native state; generated private seeds and KEM keys stay in the separate interpreter. `execute_run` recovers the whole previously checked encoded command execution, retaining the owner registry, both private pools and histories, and all shared native fields.

## Actual initialization and source connection

`PqxdhRegistrationJointOpenInitialization.client` first runs the actual existing Server-constructor program. It preserves the initialization callback, exact supplied-seed parsing, generated creation branch, rejected constructor outcome and original generator order. A successful constructor's returned public identity and private handle feed the complete existing adaptive command client. The whole program now has the same explicit open constructor/private-service interface; it does not add an initialization success or honest-identity premise.

`lifted_run` proves that forwarding the subsequent service requests through this interface preserves both private pools and the entire runtime coordinate. `initialized_run` recovers the exact previously checked initialized scheduler. `initialized_source` connects the same run to literal annotated source construction and the complete source-command execution. Its analysis output reinstalls the interpreter-private pool only after interpretation; no new secret state is returned to the original protocol adversary. `interpreted_uniform` transports the complete evaluated initialization-plus-schedule bound to the actual interpreted open program. This is an equality of whole request trees and state distributions, not a marginal public-key argument or a free ambient-work convention.

## Expanded private-service counts

The public command budget has the existing fourteen coordinates: adversarial randomness; typed Beacon creation; bundle generation; raw Server acceptance; response build; raw Beacon finish; public HMAC; public hashing; Server-kernel disclosure; and current Beacon identity, KEM, prekey, one-time and kernel reads. Every budget certificate quantifies over all typed replies and counts rejected attempts. The final initialized open program has these private capability caps:

| Capability | Complete initialized cap |
| --- | --- |
| Generated identity creation | `qCreate + (supplied.isNone ? 1 : 0)` |
| Signing | `3 qBundle` |
| Converted-identity DH | `qAccept + qFinish` |
| KEM creation | `qCreate` |
| KEM decapsulation | `qFinish` |
| Identity/KEM private reads together | `qIdentityRead + qKemRead` |
| Runtime initialization callback | `1` |
| Caller-known Server import | `supplied.isSome ? 1 : 0` |

All are upper bounds. A constructor or later operation may reject before consuming its allowance. Imported Server material does not count as a generated identity. Prekey, one-time and kernel reads remain actual local current-field projections; their lack of a private-service request is not a freshness claim or an omission of their disclosure effects. The `other` private class covers the identity/KEM reads in the actual command client; its general interface also accounts for any source request routed to that class rather than treating it as free.

`PqxdhRegistrationJointOpenCosts.coins_nonuniform` and `native_nonuniform` prove only that local work emits no private capability. They deliberately say nothing about its uniform count or CPU cost. `prefix_step`, `prefix_bound`, `prepare_bound` and `accept_bound` derive at most one static-DH request and zero other private capabilities from the actual complete collector and acceptance continuation. `serviceCost_pool` and `backend_step` expand each actual backend callback; `backend_program` preserves the whole adaptive continuation. `private_total` computes the exact closed-form expansion of the old backend ledger, adding the Server-accept DH cap once, and `command_program` applies it to the actual public command client. Its uniform coordinate is explicitly excluded from this theorem.

`PqxdhRegistrationJointOpenInitializedCosts.lifted_queries` preserves selective private counts through the constructor interface. `constructor_private` keeps the origin-sensitive generated-identity allowance; `initialized_private` joins it to the complete actual adaptive command cap. `lifted_local_free` proves that subsequent forwarded commands cannot repeat initialization or import, and `constructor_local` and `initialized_local` establish their separate whole-program caps. Local imports are ordinary operations on caller-known seed material, not a new security oracle or an assumed protocol authentication fact.

The complete evaluated uniform/base bill is retained independently. With existing KEM sampler caps `G`, `E`, `D` and an all-runtime initialization bound `qInit`, `interpreted_uniform` gives:

```text
qInit + (supplied.isNone ? 32 : 0)
+ qCoin + (64 + G) qCreate + 32 qBundle
+ (96 + E) qAccept + 64 qBuild
+ 69 max(64, D) qFinish + 64 qHmac + 64 qHash.
```

The exact source-weighted sum remains the Lean statement, with the existing `uniform_bill` supplying this expansion. It covers the actual interpreted native, KEM and base work. It is not a replacement for the final expanded Extract/HMAC/CTX cryptographic query partition. Those native operations retain their exact definitions and evaluated bill here; no ambient callback is declared free.

## Reduction interface and remaining obligations

The open initialized program supplies actual service queries for a later constructed reduction. The next simulator must distinguish caller-known imported identity slots from dynamically generated service slots while preserving source creation indices, exact public replies and the complete continuation. Public-key byte equality cannot substitute for that index mapping. Native successful signature checks must be connected to concrete public forgery reports and their actual signing/reveal history, then to the existing ordinary joint-use weak-EUF endpoint and generated-target selection accounting. These security-event and freshness/selection simulations are not proved by this operational cohort.

The scope remains the existing one-Server/many-Beacon command surface. It does not cover every Rust method: raw constructor admission, `new_onetime`, deletion, general record send/receive and the separate multi-Server imported-pending extension remain outside this surface. No snapshot, persistence or restoration behavior is included. Primitive correctness and the exact joint Ed25519/X25519 functional/security interfaces retain their existing scope; no primitive implementation is proved.

All four direct Lean 4.34 modules have exact axiom guards restricted to `propext`, `Classical.choice` and `Quot.sound` as needed. No root import, inventory, Rust protocol implementation or ProVerif model changes in this topic cohort. Independent semantic review approved the operational compiler and counts. Central semantic integration and aggregate verification remain pending.
