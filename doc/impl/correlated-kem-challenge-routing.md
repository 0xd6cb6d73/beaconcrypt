# Correlated KEM challenge-secret routing

The earlier [private-source root bound](private-source-authenticated-root.md) used a root-only post interface that blocked the challenge ciphertext. That interface cannot describe honest Beacon completion of the same Phase-2 ciphertext: even an altered ephemeral input must use the challenge shared secret locally. `PqxdhChallengeSecretRouting` constructs that routing and proves one ordinary ML-KEM IND-CCA hop while retaining the resulting correlated roots. It does not replace them by independent uniform roots.

## Primitive and private protocol interfaces

The KEM remains the existing ordinary scheme with 1184-byte public keys, 1088-byte ciphertexts and 32-byte shared secrets. `honest_decapsulation` derives the complete evaluated honest-decapsulation output from ordinary perfect correctness and actual key-generation/encapsulation support. This is a primitive correctness condition, not an authentication or secrecy conclusion.

`FunctionalDecapsulation` separately states that the opaque decapsulation operation is a pure functional response with no ambient oracle effects. `honest_decapsulation_program` combines that interface with correctness to obtain an oracle-program equality. This extra interface is essential for `route_stateful`: a mere equality of evaluated outputs would not justify deleting effects from a shared random-oracle state. Deterministic local cryptographic work still occurs in the source implementation. This module does not prove native ML-KEM code, ABI or error correspondence, and its sampled-support theorem uses the declared fixed ambient interpreter. Instantiating actual generation in a shared global interpreter remains a source-interface obligation.

`Protocol.prepare`, its retained `State`, `initialCoordinates` and `resume` describe private protocol computation inside the reduction. They are not a network-adversary API. `resume` receives the initial optional root and can make private root requests; it never receives the target KEM secret key or the supplied shared secret as an argument. The eventual Boolean is the ordinary game observation. A future native instantiation must preserve this private/public separation.

Each private request contains the unchanged ciphertext and four exact 32-byte DH coordinates. `beaconCoordinates` and `beacon_root_exact` identify the original Beacon root function for every ephemeral input. They do not bypass the role's identity, conversion, all-zero, record or state checks; those control-flow checks must govern when the native wrapper requests a root. The existing type name `KnownPqxdhRootCoordinates` means coordinates available to this private computation, not necessarily to a network attacker.

## Complete computation and correlation

`actualImpl` performs actual private decapsulation on every ciphertext. The separate ordinary public CCA channel blocks only its standard challenge query. `route` gives matching private requests the supplied challenge secret locally and forwards other ciphertexts to permitted decapsulation. Matching depends on original ciphertext bytes; no point/ciphertext normalization or injectivity is assumed.

`route_interpreter`, `route_complete` and `route_stateful` retain the complete optional root replies, arbitrary adaptive continuation and final ambient state under the checked program-level agreement. `route_challenge` confirms that a matching private request makes no ordinary decapsulation query. Failed and repeated private requests remain part of the execution.

`sourceMain` generates the KEM key, runs the private preparation, performs actual encapsulation, constructs the initial root from that secret, and continues with actual private decapsulation. `nativeMain` additionally retains the ordinary challenger's unused 32-byte sample. `source_eq_native` erases only that independent unused draw at the evaluated decision level. Costs are proved separately on both programs.

`randomMain` still performs the same real encapsulation and retains its ciphertext. One independent uniform shared secret determines the initial root and every later private root at that ciphertext, including roots with changed DH coordinates. Other ciphertexts retain actual permitted decapsulation. The fixed source function `productionHiddenRoot` is used throughout, so duplicate inputs and correlations are preserved.

`native_eq_real`, `random_eq_branch`, `correlated_indCCA` and `source_correlated_indCCA` connect these complete continuations to the existing ordinary IND-CCA game with coefficient one. No target-honesty selection premise, root-authentication assumption or prohibition of private challenge processing is added. The result concerns this explicitly constructed private protocol interface; it is not yet an instantiation of native registration and the whole Server/Beacon schedule.

## Query and computation ledger

`PostBounds` counts public uniform, base and logical decapsulation requests separately from all private root attempts. All caps quantify over every possible reply and continuation. The reduction keeps the original uniform/base caps and makes at most `dPost + rPost` logical decapsulation requests after the challenge. The bound counts matching, rejected and repeated source attempts before branching, even when the reduction locally answers them.

Let `B` and `D` bound interpreted uniform requests inside one base call and decapsulation. Let `K` and `E` bound actual key generation and encapsulation. Define `A = K + uPre + B*bPre + D*dPre + E` and `P = uPost + B*bPost + D*(dPost+rPost)`.

| Actual checked program | Uniform-request bound |
| --- | --- |
| Source execution, without ghost sampling | `A + P` |
| Actual-decapsulation challenger wrapper | `A + 32 + P` |
| Either fixed ordinary CCA branch | `A + 32 + P` |
| Ordinary fair-bit challenger | `A + 33 + P` |

One arbitrary finite uniform query counts once; the additional shared-secret sample uses 32 byte-valued draws. `actual_step_uniform`, `actual_run_uniform`, `actual_post_uniform` and `source_uniform_bound` derive source costs directly. `fixed_world_uniform_bound`, `native_uniform_bound` and `fair_uniform_bound` charge the actual challenger programs. None obtains a resource bound by rewriting only an evaluated probability distribution.

Root/HKDF evaluations, native decapsulation, fixed-width byte handling, private state and memory work are not free merely because they are functional. Every private attempt is counted; a successful private derivation evaluates the fixed root function once, and the optional initial root can add one such evaluation. Native implementation runtime, global byte budgets and the final source-schedule instantiation remain separate.

## Remaining composition

The random-secret world above is the input to further KDF analysis. The existing single-root Extract result cannot independently replace every correlated root. A subsequent proof must retain actual input equality, shared-secret reuse, duplicate and prefix correlations, adaptive context and later replies under an appropriate ordinary primitive analysis. No new tuple-output security assumption is introduced here.

Native generation/registration, role ownership, compromise policies, the private interpretation of returned role states, pinned-Server authentication and the full integrated security experiment remain open. The [joint native Gap-DH record](joint-native-gap-dh.md) describes the separate receiver-authentication primitive boundary. This checkpoint changes proof and documentation artifacts only.

## Focused validation

The final two modules and all 25 persistent dependency reports passed direct checking and an independent repeat. The full Lean build passed 3,205 jobs, the direct root check passed, and inventory validation passed with 157 handwritten Lean modules and 306 unique reviewed artifacts. The fresh transcript-fidelity suite passed all 16 tests in 12.69 seconds. Formatting, whitespace and placeholder/custom-axiom scans passed. Fresh fetched and direct `origin/vcvio` both identified `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. The two new proof modules and their additive metadata preserve all prior artifact paths and ordering; no Rust or ProVerif source changed. These are focused checkpoint results, not a new validation of the complete integrated security experiment.

## Integration into the current composition topic

The exact two proof modules from `d11e7bff48bc3d0bb52fbcc102ce3d82e4e3caf0` are semantically ported over the reviewed record-compromise checkpoint `c0555779b95563e773783d601b23faa7e1c4092a`. Their 25 persistent dependency guards pass directly and the complete combined Lean library passes 3,279 jobs. Independent review checks theorem interfaces, private challenge-secret confinement, repeated-ciphertext correlations, source versus challenger costs, exact incoming proof bytes and all 393 inventory fingerprints; the preceding 391 paths retain their order. The inventory contains 229 handwritten Lean modules. Policy, root-import, inventory and whitespace gates pass. Formatting and the sixteen transcript-fidelity tests are inherited explicitly from the immediately preceding unchanged-Rust checkpoint (12.20 seconds); this integration does not rerun or relabel those results. No Rust or ProVerif source changes, and the current user policy requires no Rust mutation run. These checks preserve the scope above: the actual authenticated source-prefix instantiation and subsequent correlated-input KDF analysis remain separate work.
