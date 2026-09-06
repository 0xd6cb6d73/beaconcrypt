# Authenticated source prefix with correlated KEM roots

`PqxdhCorrelatedRootSource` connects the actual private identity/prekey/KEM/one-time prefix and optional Server continuation to the [correlated challenge-secret router](correlated-kem-challenge-routing.md). The resulting bound has two coefficient-one terms: the existing joint-use weak-EUF advantage and ordinary ML-KEM IND-CCA advantage. Its comparison world retains one uniformly supplied shared secret for the initial root and every later private derivation at the same ciphertext. It makes no independent-root replacement.

## Source experiment and private interface

The source runs the existing generated-identity writer, complete adaptive selector and actual optional attached verification. The original seed/prekey/KEM/one-time order, private material, source query/reply history, signing/DH/reveal history, selected candidate and optional acceptance survive. The target KEM secret is erased from the continuation context and remains solely in the interpreter. `CorrelatedObserver.main` and its `ServerExecution` are private protocol computation inside the reduction; they are not network-adversary inputs. The final Boolean is the game observation.

`CorrelatedSpec` retains identity services, the ordinary CCA channel and public fixed-HKDF requests, and adds private root requests carrying an unchanged ciphertext and four DH coordinates. `localSourceImpl` preserves the complete identity state while interpreting the public KDF using the same supplied source function. `sourcePost` performs actual decapsulation for every private request, including a repeated challenge ciphertext or changed coordinates. Only the separate ordinary public CCA service applies its standard challenge block. Native role checks must still control when private protocol computation requests a root; this interface does not bypass point validation, conversion, all-zero rejection, role ownership, record checks or state checks.

`sourcePost_interpreter`, `sourcePost_complete` and `finishTarget_actual` identify the full native post computation with the correlated private interface. Optional root replies and all represented source state are retained through the original adaptive continuation. This source experiment uses the declared fixed ambient interpreter; the complete generation-order theorem is not a claim that arbitrary stateful primitive implementations commute.

## Optional branches and complete source ordering

Every accepted candidate remains in `actualGame`. Non-target, changed, disclosed, consumed, malformed and rejected candidates retain their actual branch, optional native encapsulation and observer work. Source ephemeral generation precedes optional encapsulation. Failure retains the ephemeral, absent ciphertext and unchanged registration state; the existing conversion/DH failure and final response construction follow their original order.

Only the internally recognized unchanged generated target is presented using ordinary total encapsulation. `actualGame_eq_total` derives membership in actual key-generation support before applying the existing `HonestKeyCompatibility` functional contract. Neither target selection nor native success is a premise supplied by the attacker. The equality concerns evaluated complete continuations and does not claim equal native and total primitive query traces.

`dispatch` filters only the fresh changed-acceptance event already charged to the joint-signature reduction. Completed branches execute their source observer before the ordinary challenger completes; the later unused encapsulation remains a real challenger cost. Pending state contains the original private source context and ephemeral, with no target secret or old-root-dependent response. `rootProtocol.resume` constructs the response from the supplied root and continues through the private root channel.

`dispatch_complete_eq_source` checks all completed, failed and pending cases. `filteredSource_eq_sourceMain` uses the existing `continuedSource_keyfirst` and `generators_complete_continuation` law on the entire continued computation. Moving independent KEM key generation past identity/prekey generation retains the complete generated material, selector, source state and later protocol computation; it does not use a marginal key-pair equality. Evaluated removal of completed-branch unused work is kept separate from resource accounting.

## Two-term correlated bound

`authentication_hop` applies the existing actual source-prefix authentication bound to this expanded continuation. `authenticated_correlated_bound` then applies the existing ordinary CCA router. The exact result is:

`distance(actual optional source, same-SS random source) ≤ joint-use weak-EUF advantage + ordinary IND-CCA advantage`.

The joint-signature endpoint retains the explicit converted-static-DH auxiliary service and is stronger than plain signature EUF. The original selector restrictions on extra signing and identity creation remain stated schedule obligations. There is no field, report, candidate or continuation-selection multiplier.

The CCA substitution uses ordinary perfect correctness and the existing explicit pure functional decapsulation interface. That functional interface justifies program substitution without deleting ambient effects; it is separate from IND-CCA security. All matching private requests use the same challenger-supplied secret, including those after changes to the ephemeral/DH coordinates. Duplicate inputs, shared-secret reuse and the original fixed root function remain correlated. No authentication or root-secrecy conclusion is embedded in a primitive assumption.

## Query and computation ledger

`PqxdhCorrelatedRootQueryBounds` retains all original observer requests through arbitrary possible replies. If an observer has creation cap `C`, public-source coin cap `S`, direct coin cap `U`, base cap `B`, public decapsulation cap `D` and private root-attempt cap `R`, its interpreted local interface has uniform cap `32*C+S+U`, base cap `B`, public decapsulation cap `D` and private-attempt cap `R`. The actual source and ordinary reduction charge at most `D+R` logical decapsulations. Repeated, matching and rejected attempts are counted before branching.

The generated borrowed prefix uses the already checked seed, prekey, one-time and complete selector bounds. Each dispatch class adds `qEphemeral + max(qNative,qTotal) + qObserver`; this retains actual optional non-target encapsulation and completed target failure work before the separate challenger encapsulation. The pending protocol inherits the original observer bounds, while completed and absent-root branches add no post queries.

`nativeNext_observer_bounds` specializes the actual optional continuation: uniform calls are bounded by `uEphemeral+uNative+32*C+S+U`, base calls by `bEphemeral+bNative+B`, and logical decapsulations by `D+R`. Ambient generation contributes no logical CCA decapsulation request; any internal primitive work remains covered by its separate cost contract.

`actualGame_uniform_from_calls` expands the original source prefix rather than obtaining costs from the generation-order equality. Let `Kpre`, `Kkem`, `Kone` be actual interpreted generator costs; `bCost` and `dCost` bound interpreted uniform calls inside one base operation and decapsulation. If the selector has creation/coin/base/decapsulation caps `Cs,Ss,Us,Bs,Ds`, its full prefix cost is `32 + Kpre + Kkem + Kone + 32*Cs + Ss + Us + bCost*Bs + dCost*Ds`. The actual continuation adds `uNext + bCost*bNext + dCost*dNext`, using the native optional bounds above. No unused challenger sample is charged to this original source program.

For the concrete CCA protocol, let `A = Kkem + uPre + bCost*bPre + dCost*dPre + E`, where `E` is its actual ordinary encapsulation cost, and let `P = 32*C+S+U + bCost*B + dCost*(D+R)`.

| Actual checked program | Uniform-request cap |
| --- | --- |
| Source-shaped challenger completion | `A+P` |
| Explicit correlated random-secret world | `A+32+P` |
| Native completion with unused challenger sample | `A+32+P` |
| Ordinary fair-bit CCA challenger | `A+33+P` |

`randomMain_eq_branchMain` is an exact oracle-program equality before interpretation, so it legitimately transfers the fixed ordinary branch's cost to the explicit correlated random program. `correlated_world_ledger` keeps the unused 32-byte sample and hidden-bit draw. One arbitrary finite uniform request counts once; each sampled fixed 32-byte value uses 32 byte-valued draws. Original source costs and challenger costs are proved independently.

Three original signing operations, later signing/DH/reveal/verification work, public fixed-HKDF evaluations, each successful private root evaluation, input parsing, byte copies, state histories and allocation are local computation. They do not become free because their functions are pure or because only uniform-oracle requests appear in these caps. Original observer request bounds may separately count these classes. Native runtime and global byte-budget instantiation remain later obligations.

## Remaining composition

This checkpoint closes the authenticated private-prefix instantiation of correlated KEM routing. The next KDF analysis must start from this exact same-secret world and preserve adaptive input equality, duplicate requests, prefix correlations and all later replies. The earlier single-root Extract theorem cannot independently randomize these roots.

Native registration, target-ciphertext delivery through actual Beacon/Server state, global role ownership and compromise policies, pinned-Server Phase2 authentication, correlated multi-input Extract and the final integrated security theorem remain separate. Existing primitive/source format, native/total compatibility and functional-decapsulation contracts stay explicit. No Rust, wire format, primitive implementation or ProVerif model changes are included.

## Focused validation

The final two modules and all 37 persistent dependency reports passed direct checking and an independent repeat. The full Lean build passed 3,207 jobs, the direct root check passed, and inventory validation passed with 159 handwritten Lean modules and 308 unique reviewed artifacts. The fresh transcript-fidelity suite passed all 16 tests in 11.88 seconds. Formatting, whitespace and placeholder/custom-axiom scans passed. Fresh fetched and direct `origin/vcvio` both identified `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. The additive imports, named theorem/guard gates and two new inventory entries preserve all previous paths and their ordering. No Rust or ProVerif source changed, and no full mutation suite was rerun for this proof/documentation checkpoint. These results validate the focused milestone, not the complete integrated security experiment.

## Integration with current source positions

The current composition topic semantically ports the exact two modules from `dc13f727035b997b3fbfdc15605f900b782297e2` together with the two [source-position modules](source-protocol-positions.md) from `364a62f865126d1d9299d93ffd787cc7ba303ef2`, preserving the preceding record-compromise and correlated-router work. The combined library passes 3,283 Lean jobs and all 57 added dependency guards pass directly. Independent review approves the actual optional source branches, complete generator-order law, explicit joint-use signature and ordinary CCA interfaces, separate source/challenger ledgers, and original fixed-source position invariants. It checks all 397 unique inventory fingerprints and preserves the preceding 393 paths and their order; the inventory records 233 handwritten Lean modules, 360 HB-91 statements and 48 HB-93 statements. Policy, root-import, inventory and whitespace gates pass. The unchanged Rust/ProVerif interfaces retain the explicitly inherited sixteen fidelity tests (12.20 seconds) and formatting results from `c0555779b95563e773783d601b23faa7e1c4092a`; this proof-only integration adds no Rust mutation run under the current user policy. The correlated KDF hop, actual compromise-position connection, persistent symbolic trace abstraction and final global computational interpretation remain separate obligations.
