# Joint native Gap-DH recovery and exact two-coordinate input recognition

`PqxdhJointGapDh.lean` adds an explicit DH recovery experiment and checked reductions that recognize the exact source root input. The experiment has a conventional computational recovery winning event with explicit joint signing and anchored decision capabilities. It does not assume or prove pinned-Server authentication. The receiver-side DH/hash simulation and its composition with the protocol remain open.

This component is separate from the server-side private-root result in [private-source-authenticated-root.md](private-source-authenticated-root.md). Public encapsulation lets an attacker choose a KEM shared secret while constructing a response to a Beacon. Authenticating its pinned Server therefore also requires the static DH contribution. Moreover, embedding the Beacon prekey as a DH challenge leaves `DH3 = prekey * chosen_ephemeral` unknown for arbitrary adversarial ephemeral inputs. Passing that value as a supposedly public PRF-ODH label would omit a required simulation step.

## Primitive contract and exact game

The challenger independently samples one 32-byte Ed25519 seed and one 32-byte X25519 scalar input. The existing joint primitive interface maps the first seed to its Ed25519 public key, converted X25519 public key, signatures and optional static DH. The second input has its own public-key map and optional scalar multiplication. Their ordinary functional cross-DH agreement is the only law in `DhInterface`.

The adversary receives both public challenge values. It can request signatures under the first seed and candidate tests at either challenge-held secret. A decision request contains a side selector, an arbitrary typed 32-byte peer encoding and an explicit 32-byte candidate. The answer is exactly whether that secret's actual optional DH equals `some candidate`. Neither interface returns a raw DH value. Invalid peers retain the supplied primitive's optional behavior. Every signing and decision request and reply is appended in chronological order, including failed tests and repetitions. Public random requests execute normally. Their values remain part of the adversary computation, while the service history records the signing/decision classes.

The winning event is only recovery of the actual nonzero cross-DH. `None`, an all-zero candidate and a failed target DH are proved losing. No authenticated response, accepted record, secrecy of a protocol state, target-selected-by-an-honest-party premise, or root-output distribution occurs in that event. The output distribution is the actual DH output distribution; it is never replaced by uniform 32-byte strings.

This is a specialized joint native Gap-DH recovery endpoint. Small advantage is not proved, and no hardness axiom is added to Lean. Any eventual computational assumption must name this exact joint seed distribution and signing/decision interface. Its equivalence to textbook prime-order GapDH is not claimed. In particular, an all-input bytes-only DDH relation is not imposed on X25519 representations or twist/cofactor classes. The anchored tests use the actual hidden secret. Functional peer aliases preserve the decision replies, while their original request bytes remain distinct history entries. There is no target-peer blocking rule to bypass with an equivalent encoding.

A raw static-DH secrecy interface with only the target point blocked would be unsuitable: in a prime-order subgroup an oracle response at twice the target point permits public inverse-scaling to recover the target DH. This observation concerns the hypothetical raw-DH secrecy endpoint. It does not refute the existing joint weak-EUF assumption or assert a production attack.

## Checked reductions and source relation

`scan_full` retains the complete original service history and the exact prefix of candidate tests performed by the executable first-match scan. It includes failed and repeated candidates. `scanResult_wins` identifies successful recovery with the target's occurrence among the candidates. `extraction_game` and `candidate_success_eq_advantage` preserve the original adaptive candidate-producing computation and prove exact equality between its fixed-vector candidate event and the constructed recovery game's success probability. Decision queries select the matching candidate, so this reduction introduces no guessing multiplier.

The source-input helper takes a public descriptor of two DH operations plus explicit second, fourth and KEM coordinate values. It assembles `FF32 || DH1 || DH2 || DH3 || DH4 || SS`. The input recognizer parses the first and third coordinates from the original candidate byte list, then checks equality of that entire list to the reconstruction. Thus lengths, fixed padding, known coordinates and every byte of the candidate are checked; malformed or trailing-byte inputs do not pass this check.

For a shape-compatible candidate, the executable recognizer performs both anchored decision queries and returns their conjunction. It retains both observations even if the first test fails. `testInputResult_exact` proves that its result is exactly the test that the actual optional two-DH source input equals the original candidate. `testInput_full` and `testInput_continuation` retain the complete prior and resulting history under any subsequent stateful observer. No knowledge of either hidden DH coordinate, successful plaintext or protocol authentication is a premise.

`sourceInterface` constructs the optional scalar-DH byte-model view from the existing fixed primitive function and all-zero rejection. Its functional agreement follows from the existing source wiring and DH agreement law. `assemble_source` identifies the exact PQXDH input builder. `source_target_input` gives the Beacon's two prekey-dependent calls at the converted pinned identity and original ephemeral point, with the other three coordinate values explicit. This construction does not independently prove native key generation, native additional error behavior, ABI or implementation correspondence. It also does not claim those remaining coordinates are public network observations: their calculation and ownership must be established in the actual reduction that uses the descriptor.

## Resource ledger

| Execution | Checked resources |
| --- | --- |
| Complete recovery challenger | `64 + qUniform` uniform-oracle requests, including both challenge inputs |
| Candidate scan | At most the candidate-vector length `n` decision requests; zero uniform and signing requests |
| Constructed candidate extractor | Original `qSign` and `qUniform`; at most `qDecision + n` decisions |
| Complete candidate recovery game | `64 + qUniform` uniform requests; original candidate-producing execution retained |
| One input recognizer | At most two decision requests; zero uniform and signing requests |

All syntactic caps cover every possible reply and continuation. One arbitrary finite uniform request counts once; a fixed byte vector uses one byte-valued request per byte. Decision requests are explicit oracle resources of the recovery reduction. The challenger must evaluate the requested DH and compare the candidate; signing, public-key construction, byte conversion, list/history storage and comparisons remain computation. Scanning inspects at most `n` candidates. The recognizer uses fixed-offset reads and compares a complete fixed-width reconstruction; native parser/allocation work and a final global byte/runtime budget are not established here.

## Relation to existing literature and remaining work

The standard PRF-ODH family provides derived-output oracles for related DH inputs; its variants differ in oracle access and challenge timing. Its HMAC/Extract treatment includes swapped key/input usage under a compression-function random-oracle model. Those results are relevant methodology, but do not directly supply this native joint signing distribution or the correlated two-coordinate source simulation. [Brendel, Fischlin, Günther and Janson, sections 2 and 6.3](https://eprint.iacr.org/2017/517.pdf).

The PQXDH specification describes GapDH/hash-random-oracle analyses while explicitly identifying joint signing/DH key reuse as an outstanding primitive-composition issue. The published formal-analysis artifact also records its key-separation simplification. Neither result is imported as a proof of BeaconCrypt. [Signal PQXDH specification](https://signal.org/docs/specifications/pqxdh/), [PQXDH formal-analysis artifact](https://github.com/Inria-Prosecco/pqxdh-analysis).

The present theorem supplies an exact input recognizer, not a complete hash-output simulation. Remaining work must preserve the same actual hash inputs and all derived outputs, handle every source role and shared secret use, justify the concrete Extract/ROM boundary, connect the actual target prekey generation and joint seed interfaces, and compose native ownership, compromise and record freshness. No bespoke tuple-output security assumption replaces those obligations. The whole global experiment is still pending.

The existing KEM root theorem's challenge-blocked post interface is also still a source policy boundary. Actual Beacon processing of the same challenge ciphertext, including altered ephemeral inputs, must use the supplied CCA shared secret locally and preserve the resulting correlated roots. It must not be ruled out by a freshness condition or require a forbidden challenger decapsulation query. Private `ServerExecution`/owner states remain interpreter state; they are not network-adversary arguments. This component does not close that separate routing and correlation obligation.

## Focused validation

The final module and all 39 persistent dependency reports passed direct Lean checking and an independent repeat. The complete proof build passed 3,203 jobs, the direct root check passed, and the inventory passed with 155 handwritten Lean modules and 304 unique reviewed artifacts. The fresh transcript-fidelity suite passed all 16 tests in 13.60 seconds; formatting, whitespace and placeholder/custom-axiom scans passed. The inventory command initially encountered the environment's absent `/bin/bash`; rerunning the unchanged gate with `SHELL` set to the available Bash passed. Fresh fetched and direct `origin/vcvio` both identified `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. No Rust, protocol-model or mutation inputs changed. These are this focused component's checks, not a new validation of the complete integrated protocol experiment.
