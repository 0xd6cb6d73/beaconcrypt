# Independent refinement review

## Review scope

The representation workstream independently inspected the live protocol composition and server transaction files after the beacon completion milestone `001b4e8`. This is a statement-level and proof-structure review, separate from the author and coordinator build gates. The ratchet workstream independently reviewed `RepresentationBridge`, `ByteTraceRefinement`, and `BoundaryExecution` in the opposite direction; those reviews reported no blocking issue.

## Beacon protocol findings

The new `completeBeacon_refines` theorem does not assume an ideal receive result or a desired registration refinement. `BeaconBoundary` identifies the typed inputs with successful primitive conversion/decapsulation results, shared DH values, identities, and wire identifiers/sequences. Root and initial/ongoing HKDF premises are local primitive representation equations.

The proof connects extracted candidate preparation to exact root transcript and association bytes, derives the root from that candidate, runs the actual initial phases, and invokes the actual receive driver on that initialized kernel. `recvStep_commutes` supplies the byte-model plaintext/error and represented poststate. The authenticated plaintext parser preserves the first eight bytes exactly, and extracted binding authentication and commit determine the assigned identifier and pinned binding.

Every included beacon outcome is represented: pinned-identity mismatch, zero DH, bad sender, zero sequence, record rejection, short plaintext, binding mismatch, and success. Record rejection includes malformed/authentication failure and skip/admission rejection at the receive API's absent-plaintext projection. Success retains the complete ratchet states, while failure corresponds to the ideal aborted registration. Decapsulation/conversion failure and the ideal `notInitSent` alternative are outside the typed supplied-input boundary and must not be claimed as core executions.

The handwritten driver includes sender/sequence guards and the authenticated plaintext length/prefix parsing needed to compose the public extracted phases. Its theorem is about this explicit synchronous API sequencing, not all arbitrary low-level phase calls or the surrounding Rust adapter. The actual library implementing that sequencing remains an external correspondence obligation.

At this review checkpoint, the relation supplies sufficient origin/send/receive witnesses to start `ByteTraceRefinement`. An explicit theorem composing successful registration with arbitrary ongoing histories was requested from the protocol workstream, so the final integrated claim does not rely only on parallel initialization and history theorems.

## Server findings

The live `initialize_send_refines` statement connects actual server initialization and first-send phases to the exact byte-model record and advanced send state, with the complementary empty receive state. It uses a specified successful record interpretation, rather than a premise asserting a successful desired refinement. The extracted wire sequence is converted to the model index; the initial send relation supplies sequence one and index zero. The helper was still being completed by its author at this review checkpoint, so final validation is not asserted here.

`failed_candidate_differs_from_atomic_emit` identifies a real strict-refinement obstruction: with an available nonexhausted identifier, unchanged ideal `serverEmit` advances the allocation counter, while a failed concrete candidate seal returns the old counter. `finishCandidate_failed` also discards the transient advanced ratchet. The `idealPublication` abort closure records failure at the already consumed replay-token prefix and preserves its entire state; success and rejection retain the full ideal response/error and state. Its preservation rule correctly requires a property at that prefix as well as after atomic emission.

At this checkpoint, the failure and ideal-prefix results were separate local theorems. A complete server publication claim additionally needs a candidate-to-prefix relation identifying counter, root, identity, associated data, record inputs, and the external peer/replay-token bookkeeping absent from `beaconcrypt-core`. This was reported to the coordinator as an integration obligation. The strict atomic counterexample must remain explicit; the abort closure cannot be presented as equality with the original atomic transition.

## Property-transfer review

The byte and callback trace statements preserve complete public invocation fields, full records and plaintexts, failure observations, and related final byte states. Their transfer theorem is for universal finite predicates proved on the explicitly defined byte API wrapper. Properties of raw ideal atomic steps require a separate argument that they tolerate withheld failed sends and explicit API stutters. Neither the model-property premise nor the primitive-callback contracts assert implementation refinement. Infinite liveness, probabilistic security, hyperproperties, compiler/extraction faithfulness, external library correctness, and memory erasure are outside these finite behavioral statements.
