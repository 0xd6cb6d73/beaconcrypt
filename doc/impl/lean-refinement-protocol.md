# Protocol composition milestone

## Audited baseline

The audit inspected the actual `vcvio` definitions in `PqxdhProtocol.lean`, `PqxdhSession.lean`, `PqxdhConcreteSession.lean`, `PqxdhSessionLifecycle.lean`, `RatchetReceiveIdeal.lean`, the PQXDH ideal model, and extracted `Funs.lean`. The ideal models remain unchanged.

`honest_run_refines` composes the extracted registration bookkeeping and proves assigned identifiers, associated data, and pinned bindings, but it does not execute concrete key initialization or first-record receive. `beaconFinishDriver_refines` assumes a successful ideal receive equation; therefore that theorem cannot establish the first-record link. `initial_kernels_refine` executes initialization but accepts an arbitrary concrete ratchet interpretation, so the existing byte-origin assertions do not themselves connect later record behavior to PQXDH's byte interpretation. `authenticated_registrations_establish_concrete_session` assumes root-input agreement and concludes an invariant. These are useful prerequisites, not a completed behavioral registration refinement.

The current extracted core has no `initialize_ratchet_keys` symbol. Its public key-initialization surface is `start_beacon_ratchet_kdf`, `start_server_ratchet_kdf`, candidate-specific start variants, and `resume_initial_ratchet_kdf`, which calls the extracted byte split and `ConcreteRatchetKernel.new`. The maintained `initializeBeacon` and `initializeServer` drivers sequence exactly these phases.

## Agreed interface

`RepresentationBridge` owns `absChain`, `absMaterial`, `recordCrypto`, `concreteCrypto`, the ongoing 76-byte `KdfLaw`, `mapSend`, `mapRecv`, and exact send/receive commuting theorems. This workstream owns the initial 64-byte `InitialKdfLaw`, `RootKdfLaw`, and protocol drivers. The laws interpret concrete primitive requests by the unchanged PQXDH cryptographic interpretation; they do not assume protocol or ratchet refinement.

## Acceptance criteria

1. Execute extracted initialization and establish related full ratchet states under the shared byte interpretation.
2. Execute the actual receive driver for every typed wire sequence and ciphertext, including zero sequence, malformed/authentication rejection, replay/capacity rejection, and successful first-record processing.
3. Compose extracted registration preparation and authenticated commitment with those phases, preserving the existing ideal guard outcomes and state transitions for every included registration result.
4. State primitive input, serialization, and adapter sequencing assumptions explicitly. Do not claim that the surrounding Rust library realizes a handwritten driver without an independent correspondence proof.
5. Derive ideal receive outcomes and state relations, rather than accepting an ideal receive equation as a premise.

## Ledger

- Proved baseline prerequisites: extracted initial split and kernel construction; concrete receive behavior under one fixed concrete primitive interpretation; registration bookkeeping case theorems.
- Newly proved and locally Lean-checked: `initializeBeacon_refines` and `initializeServer_refines` execute extracted initial phases under `InitialKdfLaw`; `prepareBeacon_refines` supplies exact candidate root, AD, binding, and identifier; `commitPlaintext_eq` covers malformed plaintext, key-binding mismatch, and success; `initialize_receive_refines` composes actual initialization with `receiveNext` and the shared byte bridge, preserving complete plaintext outcomes and represented poststates for every positive sequence without a successful-receive premise.
- Legitimate boundary obligations: fixed root and initial/ongoing HKDF interpretation; actual record sealing/opening agreement with the byte record model; correctly supplied primitive results and typed inputs at the core boundary.
- Newly proved: `completeBeacon_refines` covers every included beacon completion outcome against the unchanged `Pqxdh.beaconFinish`: identity mismatch, zero DH, wrong sender, zero sequence, receive admission or authentication rejection, short authenticated plaintext, wrong authenticated key binding, and success. Failure preserves the exact ideal error and aborted state. Success preserves the identifier, pinned binding, associated data, and complete represented send and receive states. No successful ideal receive equation is a premise.
- The beacon completion milestone is complete within `BeaconBoundary`; the server transaction milestone remains separate and is not implied by this result.
- Independently confirmed server mismatch: a failed first seal leaves the replay token consumed but publishes no peer and does not increment allocation; the unchanged atomic `serverRespond` has no such outcome. The coordinator owns an explicit abortable transaction-prefix interpretation and a counterexample to the strict atomic claim. This workstream must not hide that mismatch by claiming complete server correspondence.

## Beacon proof explanation

The driver first calls extracted `beacon_prepare_finish`. Its success theorem identifies the complete root transcript, associated data, assigned identifier, and pinned server binding. `RootKdfLaw` therefore turns the actual derived root into the ideal beacon root, rather than assuming that the two protocol roots agree. `InitialKdfLaw` then interprets the request emitted by the extracted candidate initializer. The initializer theorem supplies the concrete zero-counter kernel and exact directional byte origins. The ongoing `KdfLaw` and representation bridge carry those origins through `receiveNext`, giving the exact ideal plaintext result and full ratchet poststate for every admitted positive sequence.

The driver checks sender and zero sequence before initialization and record opening, matching the unchanged ideal guard order. These are explicit operations of the documented handwritten core driver. The proof does not claim that the surrounding Rust adapter uses this ordering. On authenticated plaintext, `plaintextBinding` converts precisely the first eight bytes back to an extracted array, with a proved byte round trip. The driver calls extracted `authenticate_registration_key_id_binding` and `beacon_commit`; `commitPlaintext_eq` proves short-plaintext, binding-mismatch, and success behavior. Combining those facts produces `completeBeacon_refines` without assuming the desired receive or registration result.

`BeaconBoundary` states only the interpretation of values actually supplied at the core boundary: successful decapsulation, successful identity-key conversion, the four DH outputs, the beacon public identity, and exact response identity/identifier/sequence fields. Failures of decapsulation, signature checks, malformed wire parsing, or public-key conversion occur outside these typed core inputs and remain adapter obligations. This does not exclude any outcome of the included `BeaconInitSent` completion driver. It does exclude calls from other protocol states, which cannot be expressed by this driver input type. The fixed pure record interpretation calls the unchanged PQXDH record model on all key, nonce, associated-data, and ciphertext bytes; actual AEAD/CTX implementations remain a separate primitive boundary.
