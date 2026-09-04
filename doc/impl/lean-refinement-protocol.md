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
- `completeBeacon` and `BeaconBoundary` are defined and checked. Unresolved at this milestone: proof that the full driver matches `beaconFinish` across preparation, sender, zero-sequence, receive, plaintext, and binding outcomes. The overall registration milestone is not yet complete.
- Independently confirmed server mismatch: a failed first seal leaves the replay token consumed but publishes no peer and does not increment allocation; the unchanged atomic `serverRespond` has no such outcome. The coordinator owns an explicit abortable transaction-prefix interpretation and a counterexample to the strict atomic claim. This workstream must not hide that mismatch by claiming complete server correspondence.
