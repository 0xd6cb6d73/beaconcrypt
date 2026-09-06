# Replicated source record interface

HB-93 connects the checked Server and Beacon record operations to one concrete cryptographic backend. It covers arbitrary adaptive calls to the supplied role instances, raw delivery, original optional API replies, public randomness, public commitment queries and real public HKDF projections. Twenty statements preserve complete execution and derive aggregate query bounds across both roles. This is the record-operation part of the common experiment; allocation, registration, explicit reveals, snapshots, network observation and the cryptographic hybrid simulations still need their own connections.

## One concrete source and one primitive state

`RawCtxProtocolBackend.backend` fixes the private KDF callback to `RawCtxSourceHkdf.kdfImpl source`. Public and private HKDF operations therefore use the same supplied HKDF-SHA-512/no-salt function, with the exact existing input and label representation and shared-prefix contract. `private_hkdf` returns the actual complete 76-byte native response and preserves the entire auxiliary/cache state. `public_hkdf` returns the requested projection from that same fixed source. Repeated inputs and projections retain their original correlations. No public HKDF random table or public-HKDF/random-table security advantage appears.

`server_schedule` instantiates the previously checked Server/public complete-state equation with this concrete callback. `server_uniform` specializes its ledger to `U+64(S+R+H)` uniform-oracle calls. Deterministic native HKDF and functional AEAD work remain real primitive evaluations. HMAC-SHA-512 and the BLAKE2b commitment interface remain separate algorithms; this construction does not route HMAC internals through the CTX table.

The shared primitive state contains the same auxiliary state and CTX cache used by sealing, opening and public commitment requests. Failed lookups and opening attempts retain their actual effects. The fixed-source presentation uses the previously stated total functional AEAD, total CTX ROM and optional functional writer contracts. Those functional/ROM contracts are distinct from ordinary collision resistance and from the cryptographic security games.

## Complete role families and actual source operations

`RawCtxRoleFamily.familyImpl` selects one complete role state by its typed instance handle and reinstalls only that instance's returned state. All other instances and their private fields remain in the result. `sourceFamily` invokes the existing actual source handler with the same selected state and the single current primitive state. `family_interpretation` proves that primitive interpretation commutes with this routing; `schedule_interpretation` lifts the equation through every adaptive continuation and final stopping decision.

The initial family is an arbitrary function from `Fin count` to complete role states. It may contain equal identities, shared roots, repeated materials or other correlations. No product-distribution, generator-order interchange, independent-key premise or source-key injectivity is used. `step_bound` proves that selecting an instance adds no primitive calls. `server_interpretation` and `beacon_interpretation` instantiate the generic equation with the existing actual Server peer-map and Beacon lifecycle handlers.

`Fin count` identifies supplied API instances. It does not bound a peer's hostile machine identifier or restrict raw record bytes: those continue through the original parser, route, pin, associated-data and receive-window checks. The interface does not create instances. Its fixed-state execution cost begins after the supplied initial state exists, so identity/KEM generation and initialization costs must be added when connecting the source prefix. They are not declared free. A zero family has no callable instance handles, while the public services remain available independently.

`RawCtxProtocolRoles.protocolImpl` combines both families and public services in one interface. Every Server or Beacon call uses the same concrete backend. Public coins and public hash/HKDF requests are outside either family, and preserve the role states while retaining their actual primitive effects. `protocol_interpretation` identifies each combined operation with the existing selected source handler. `schedule_interpretation` proves equality of the full adaptive cross-role execution, retaining the result, both complete families, auxiliary state and shared cache up to tuple reassociation.

Server calls retain the actual same-peer identity/associated-data lookup and whole-kernel publication. Beacon calls retain all five lifecycle variants and admit record operations only from the established variant. The actual outer identity ID supplies the encoded sender; the pinned control and stored associated data keep their source roles. No agreement between later outer IDs and assigned IDs is assumed. Rejection, source failed-send advancement, receive rollback, consumed-key replay behavior and the original optional plaintext follow the already checked local handlers.

Complete state in these equations is private analysis state. It is not added to the adversary's observation. The raw API's actual optional plaintext is a privileged application reply; an enclosing network experiment must state which replies it discloses and which target-plaintext disclosures violate freshness. These execution equations alone do not prove secrecy against an observer explicitly given the target plaintext.

## Aggregate query ledger

`RawCtxProtocolBudgets.Bounded` supplies five structural budgets over every possible reply continuation. Let S count sends across both roles, R raw API attempts, U caller uniform requests, H public commitment requests and K public HKDF projection evaluations. Invalid and repeated operations consume their original source budget coordinate. `source_bound` projects each coordinate to an ordinary selective query bound, including the K deterministic public HKDF calls.

`backend_step` derives per-operation native costs from the actual selected source helper. `weighted_bound` composes those costs through the whole adaptive stateful program. `backend_bound` and `backend_bounds` give the following common native ledger:

| Quantity | Bound |
| --- | --- |
| Native ratchet KDF callbacks | S + 51R |
| Native AEAD seals | S |
| Native AEAD opens | R |
| Shared private/public commitment queries | S + R + H |
| Native writer callbacks | S |
| Public fixed-HKDF projection evaluations | K |
| Caller uniform requests | U |
| Complete interpreted uniform-oracle calls | U + 64(S + R + H) |

The 51 receive coefficient is the existing source window bound, including failed attempts and arbitrary represented entry states. A repeated derivation remains a KDF call even when it requests a previously used chain position. The operational bounds have no additional instance-selection factor. This does not remove target/session/record selection losses from the still-required cryptographic reductions.

`RawCtxProtocolUniform.beacon_uniform` counts the possible commitment-cache miss in each actual Beacon record call. `beacon_source_uniform` transfers that bound through the exact source tuple representation. `source_step` combines both roles and all public services with the same primitive state. `schedule_uniform` proves the final displayed uniform cap through every adaptive continuation.

The aggregate unit is a uniform-oracle call. A 64-byte CTX miss uses 64 byte-valued calls; a caller may request another finite range. Cache hits and earlier failures can use fewer calls. Fixed HKDF, functional AEAD and writing have zero additional uniform requests in this interpretation, while their primitive evaluations, input lengths, byte conversions, parsing, copies, maps and supplied local computation retain actual work. The separate KDF, public HKDF, AEAD and writer counts are not replaced by a claim of zero computation. This ledger does not bound compiled instruction counts or allocator/parser traversal cost.

## Remaining composition and trust obligations

Native primitive/library representations, reader/writer outcomes, map and slot behavior, synchronous ownership, compiler/runtime and the already stated functional source contracts remain at their documented boundaries. Persistence integrity, rollback resistance, linearizable CAS, crash behavior, physical erasure and foreign-runtime ownership/copies remain explicit deployment premises; the unkeyed snapshot digest does not supply them.

The enclosing common experiment must still construct the supplied role states from actual identity/registration prefixes, model mutable registration and attacker-owned identities, connect permitted reveals and restores, and distinguish privileged API replies from public network observation. The key-position and evolving-chain layers must link actual installed materials to the correlated KDF games, including retries, erased past state and copied material. Multi-key CTX, KEM challenge-secret reuse, joint identity use, target freshness and all adjacent security hybrids must then operate in that same experiment. These twenty operational/resource statements do not themselves establish those cryptographic conclusions, post-compromise recovery or the final computational interpretation of every ProVerif event.

## Milestone validation

The five changed modules passed direct Lean checks with all twenty persistent dependency guards. The complete library built successfully with 3,272 jobs. Independent review rechecked all twenty guards, theorem statements, complete-state equations, source and native query ledgers, every one of the 386 inventory fingerprints and the preserved order of the prior 381 entries. The inventory contains 222 handwritten Lean files. Repository Lean policy/root checks, `cargo fmt --all -- --check`, `git diff --check` and all sixteen transcript-fidelity tests passed; the fresh fidelity run took 14.21 seconds. The milestone changes no Rust implementation or ProVerif model, so it requires no Rust mutation run under the user's current validation policy. Final global integration still requires its complete matrix on the actual final merge result.

## Reviewed component integration after HB-93

The next union retains the twenty HB-93 statements and semantically ports three separately reviewed modules without changing their bytes: 39 statements from `PqxdhJointGapDh` at `fb8a1ace9551da1ab349eaf62ed1fea32693f1df`, 21 from `KemValueClasses` at `7389d6f42924e48e462c766e7ec38d29e865d665`, and 30 from `RawCtxMaterialPositions` at `a8d3209b67e56f68a1686b84cbd4b59300ab160d`. Their linked records explain the exact joint recovery game, actual-value equality representation and fixed-source position/refinement scope. The input recognizer supplies no derived-output simulation; private value classes supply no ProVerif process simulation; real source positions supply no independent-key hybrid. Those remaining connections are unchanged by their integration.

The combined library passes 3,275 Lean jobs and direct checks of all ninety incoming dependency guards. Independent integration review verifies every one of the 389 unique inventory fingerprints, preserves the preceding 386 paths and their order, confirms the exact root-import union and retains every prior checker rule apart from the additive handwritten-Lean count of 225. The HB-91 operational inventory now has 348 statements, while HB-93 retains twenty; the distinct HB-92 actual-value row is added without claiming completion of the symbolic interface. Inventory, Lean policy/root and whitespace gates pass. The unchanged runtime/model files retain the immediately preceding fresh sixteen-test fidelity and formatting evidence; this proof-only union does not relabel it as another run or require Rust mutation testing. The source tree and the older topic documentation remain preserved; shared metadata is reconciled semantically.
