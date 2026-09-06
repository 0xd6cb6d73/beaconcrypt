# Private source generation and authenticated server-side root

This checkpoint connects the generated-identity signature reduction to the all-candidate optional KEM/root execution in one typed source experiment. `PqxdhPrivateRootSource.authenticated_root_bound` gives four coefficient-one terms: joint-use weak-EUF, ordinary ML-KEM IND-CCA, the exact correlated secret-input Extract experiment, and one-query HMAC PRF. It preserves the complete private setup, source histories, candidate result and root-dependent continuation. It does not establish Beacon-side authentication of the pinned Server or the final global protocol theorem.

## Actual execution and the reduction boundary

The source creates one identity, samples the prekey, samples the ML-KEM keypair, samples the one-time key, signs the original prekey/one-time/PQ messages, runs the adaptive selector, and returns the actual optional attached-verification result. `program_complete` is an equality of complete probabilistic programs, including the generated secret state and every source history. The selector may make ordinary prechallenge decapsulation calls and public identity/DH/reveal/candidate requests. The coefficient-one authentication theorem requires its explicit zero-extra-signing and zero-extra-creation caps. It derives the exact three-message log and index-zero membership; neither an honest selected candidate nor an externally supplied signing log is assumed.

Protocol-private coins use a separate channel. `compile_complete` preserves the complete result and identity state while restoring only synthetic logging of private coins introduced by the reduction. Original public coin/reply observations remain in order. This equality concerns `BareState`; it is not a claim that synthetic reduction positions are native public report positions. Generated KEM secrets are available only to the local primitive interpreter. `eraseGenerated`, `eraseRetained` and `eraseOutput` remove that field before the borrowed root continuation; no secret is passed as a selector argument.

`continuedSource_keyfirst` commutes only the independent KEM keypair and retains the whole subsequent evaluated continuation. The fixed stateless ambient interpreter is explicit. Actual generation costs are proved on the original program before this evaluated interchange; output-distribution equality is not used to infer equality of primitive query traces.

Every candidate follows the actual optional source interface. Rejected or other-key candidates keep their real replies and complete effects. Eligible targets generate the source ephemeral before optional encapsulation. Replay/root failures, registration consumption and subsequent root-dependent response construction use the existing typed source functions. Honest-key membership follows from the actual generated support. Only then does `actualGame_eq_total` apply the stated native/ordinary functional compatibility. Native rejection at arbitrary submitted keys remains possible.

The root input is exactly 192 bytes: 32 bytes of `FF`, four actual source DH coordinates, then the 32-byte KEM secret. `rootInitializer_input` identifies this source input. The pending context contains no response derived from an old root: `finishTarget` constructs the response and publication from the supplied root. Completed branches may generate ignored challenger encapsulation/secret and dummy input draws after the source observer has already returned; those operations are explicitly accounted and do not claim to be native protocol work.

The successful eligible target's actual experiment installs `blockChallenge` in its post interface. Prechallenge and common/completed source work retain unrestricted ordinary decapsulation. The pending post interface blocks the exact target ciphertext and retains every attempted call in its logical cap. Mapping unrestricted native post-root traffic to this interface remains a protocol freshness/operation obligation.

## Checked components

| Requirement | Establishment |
| --- | --- |
| Private coins, original public logs and full state | `PqxdhPrivateSourceCoins.compile_step`, `compile_complete`, `privateRun_eq` |
| Actual optional candidate and its final detector | `PqxdhPrivateCandidateAcceptance.candidateProgram_complete`, `compiledCandidate_last`, `compiledCandidate_recorded` |
| Private generation order, target support, borrowed selector | `PqxdhPrivateKemSource.generate_key_support`, `source_generation_complete`, `localSelector_complete`, `generators_complete_continuation` |
| Full source signing/reveal/seed histories | `PrivateSourceInvariants.private_run_noSign`, `private_run_created`; `PqxdhPrivatePhase1Prefix.program_complete`, `program_supported` |
| Changed actual acceptance to one joint-use forgery | `PqxdhPrivatePhase1Prefix.authentication_bound`, `authentication_continuation_bound` |
| Source optional encapsulation and full root equality | `PqxdhPrivateRootSource.nativeTarget_eq_total`, `actualGame_eq_total`, `continuedSource_keyfirst`, `filteredSource_eq_initializerReal` |
| Exact source root and arbitrary supplied-root continuation | `rootInitializer_input`, `finishTarget_real`, `dispatch_finish_eq_source` |
| Four-term computational bound | `authentication_hop`, `authenticated_root_bound` |
| All logical source/CCA/post classes | `PqxdhPrivateKemQueryBounds`, `PqxdhPrivateRootQueryBounds` |
| Actual source and complete ordinary challenger sampling | `PqxdhPrivateRootGameBudgets.program_uniform_from_calls`, `actualGame_uniform_bound`, `oneKeyBranch_uniform_bound`, `oneKeyFairProgram_eq`, `oneKeyFairProgram_uniform_bound`, `initializer_uniform_ledger` |
| Concrete Extract and HMAC world sampling | `SecretInputKdfWorldBudgets` |
| Same joint-EUF reduction, private coin cap, signing3 and attempted DH | `PrivateSelectorCoinBudgets`, `PqxdhPrivateRootEufBudgets.program_class_bound`, `privateReduction_uniform_ledger`, `privateReduction_sign_bound`, `privateReduction_staticDh_bound` |

## Resource ledger

All uniform quantities count oracle calls. A general finite-range request costs one call; the explicitly sampled fixed byte vectors cost one call per byte. Let `B` bound the complete interpreted uniform work of one base request and `D` that of one decapsulation, including rejected replies. `evalKem_uniform_bound` expands a CCA client's caps as `u + B*b + D*d`. No opaque base or decapsulation work is assigned zero cost.

Let `G = prekeyCoins + keygenCoins + oneTimeCoins` and `S = selectorSourceCoins + selectorCcaCoins + B*selectorBaseCalls + D*selectorDecapCalls`. The actual prefix costs `32 + G + 32*selectorCreates + S`; the security theorem's zero-extra-creation schedule sets `selectorCreates = 0`. The syntactic private-program coin budget is `G + S` and excludes the identity service's internal creation draw. The signature reduction separately pays its actual challenger seed, so its complete coin ledger is `32 + G + S` and includes that seed exactly once. Signing is capped at three, and the 1,253 source signed-message bytes remain the unchanged writer workload.

For each CCA class, the actual native continuation has cap `ephemeral + nativeEncapsulation + observer`. The reduction prefix instead has `borrowedPrefix + ephemeral + max(nativeEncapsulation, totalEncapsulation) + observer`: a completed target-abort branch can perform ordinary encapsulation before the challenger's separate encapsulation. The borrowed prefix charges its identity seed, prekey, one-time key and entire selector; the challenger generates the target KEM key separately. Source post coins include `32*postCreates + postSourceCoins + postDirectCoins`. Direct post base, attempted decapsulation and public root/symmetric KDF caps remain separate. Repeated, rejected and blocked calls remain charged.

Write `Q = keygenCoins + preUniform + B*preBase + D*preDecap + encapsulationCoins` and `P = postUniform + B*postBase + D*postDecap`. These are obtained from the actual logical prefix/post lemmas and explicit primitive costs. The ordinary encapsulation in `Q` occurs on every branch, including completed branches.

| Complete program | Uniform-call cap |
| --- | --- |
| Secret-input sampler | `Q + 32` |
| Fixed real or false KEM world | `Q + 32 + P` |
| Exact ordinary fair-bit KEM challenger | `Q + 33 + P` |
| Source-root and real Extract worlds | `Q + 32 + P` |
| Independent-root world | `Q + 64 + P` |
| Uniform-PRK Extract world | `Q + 96 + P` |
| Ordinary real HMAC world | `Q + 96 + P` |
| Ordinary random HMAC world | `Q + 96 + P` |

The HMAC reduction itself makes one challenge query and `Q + 32 + P` local uniform queries. The real HMAC challenger samples a 64-byte key; the random HMAC challenger samples one 64-byte output and no key. The independent root adds 32 bytes, and uniform Extract adds the full 64-byte PRK. Native/ordinary compatibility constrains evaluated outputs on honest support, so native and ordinary encapsulation costs are deliberately separate.

Deterministic signing, converted DH, attached verification, source DH/root/response functions, byte processing and history scans are still local computation. Source service/candidate/reveal caps charge every attempt; input sizes and primitive runtimes remain explicit runtime parameters. These uniform-call theorems do not assert native instruction counts, parser allocation/traversal bounds or constant-time behavior.

## Primitive and source contracts remain distinct from protocol results

The primitive endpoints are the explicit joint-use weak-EUF game with chosen optional static-DH service, ordinary ML-KEM IND-CCA, the exact joint fixed-salt Extract game, and ordinary HMAC PRF. The first is stronger than plain signature EUF. Extract is tested on the complete actual correlated sampler; it is not replaced with a public HKDF random table or a `q/2^256` hidden-input argument. No primitive implementation or negligibility theorem is proved here.

Ordinary functional contracts connect attached verification/parsing, honest-generated native/total KEM outputs, source DH/public conversion and fixed-HKDF Extract/Expand. Perfect primitive correctness does not itself imply those source-interface identifications or computational hardness. In particular, compatibility is applied after proving honest support; it does not assume that the selector chose honestly and does not follow from IND-CCA.

Native generation/secret representation, Cap'n Proto decoding and publication, identity byte-owner lookup/collisions, once-only lifetime signing and general stateful global primitive interpretation remain separate source or deployment boundaries. This checkpoint is the server-side KEM-backed root branch. An attacker can construct its own encapsulation toward a Beacon while lacking the pinned Server's static-DH contribution, so Beacon-side Phase2 authentication requires a distinct actual-DH/derived-output reduction. A raw static-DH secrecy oracle with target-point blocking is unsuitable: related valid inputs can recover the target DH value. No such assumption is introduced here.

A common experiment must still compose all sessions, native operations, chain/key handles, adaptive records, snapshots, compromise/reveal policies and observable outputs. Sibling reviewed components and their historical validation do not establish that final union. The representation-alias regressions remain model-fidelity evidence, not an end-to-end security completion endpoint.

## Focused validation

The final copied graph passed `lake build` with 3,202 jobs and all 123 persistent axiom reports across the twelve added modules; the direct root-module check also passed. The inventory gate and an independent full rehash passed for 154 handwritten Lean modules and 303 unique manifest artifacts. Fresh `proverif_transcript_fidelity` passed all sixteen tests in 13.02 seconds. Formatting, whitespace and forbidden-placeholder/custom-axiom scans passed. Freshly fetched and directly queried `origin/vcvio` both remained `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. Runtime/PV source and their mutation inputs are unchanged. Historical sibling protocol/mutation runs are not relabelled as new validation of this graph; the final reconciled integration matrix remains required.
