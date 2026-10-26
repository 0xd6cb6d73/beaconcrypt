# Byte trace refinement milestone

## Agreed scope and semantics

`BeaconcryptCore/Refinement/ByteTraceRefinement.lean` lifts the extracted synchronous ratchet driver to the unchanged `Pqxdh.ratchetCrypto` byte model. It imports the representation bridge and the observable ratchet operation/history milestone. It does not edit the ideal models.

`ByteRoleState` includes both chain byte strings, both logical counters, and every skipped key and nonce. `ByteAction` retains associated data, complete plaintext/ciphertext byte strings, the actual wire sequence, and the chosen external sealing outcome. `ByteObservation` is the ratchet API observation instantiated with full byte strings. A sent observation carries the logical index and complete record; a seal failure carries the consumed index; counter exhaustion and invalid sequence zero are separate outcomes. Receive observations retain the complete optional plaintext. The underlying core receive API returns an absent plaintext for all rejections, so the wrapper retains exactly that API granularity. The lower representation theorem retains all ideal receive error distinctions before that public API projection.

`byteAction` wraps unchanged ideal `sendStep` and `recvStep`. A failed sealing attempt performs one ideal send whose record is withheld while its index and state advance remain observable. Counter exhaustion and zero wire sequence are explicit unchanged-state transitions. `byteTrace` records exactly one observation for each invocation. These wrapper semantics are defined in the refinement layer and make implementation/model mismatches explicit without changing the ideal model.

## Proved

- `action_commutes` and `trace_commutes` connect the existing concrete-type ideal API interpretation to the PQXDH byte interpretation with identical complete observations and represented states.
- `executeTrace_refines` proves termination and existence of a corresponding byte execution for every finite mixed history starting from `ByteKernelRefines`.
- `executeTrace_observed` applies to every actual completed extracted driver evaluation, rather than only to a chosen existence witness.
- `transfer_finite_property` transfers any universal predicate over finite action traces, exact observation traces, and represented final byte states. It supplies the related final state itself.
- `byteAction_recvWf`, `byteTrace_recvWf`, and `executeTrace_recvWf` demonstrate property transfer using the unchanged model's receive invariant: at most 50 skipped keys, all skipped indices precede the receive counter, and no index is duplicated.
- `sealNext_callback_refines` covers actual optional seal callbacks whose successful returns satisfy the record primitive contract. Failure is unrestricted. It determines a matching Boolean outcome from the actual callback result and relates the actual kernel/output to the byte API result, including exhausted and key-consuming failure paths.

## Assumptions and property classes

The ongoing HKDF boundary is precisely `KdfLaw`: the actual 76-byte request receives the byte-model HKDF result on that chain and label. The record interpretation is `recordCrypto`; external open/seal implementations must implement the model's complete record operations, including byte encodings, AEAD, CTX, and associated-data handling. Cryptographic implementation correctness and security, the surrounding library, runtime/compiler correspondence, and extraction faithfulness remain separate boundaries.

The trace theorem covers finite sequences of complete synchronous operations composed from extracted begin/resume/finish functions. The receive driver's existing finite-execution equivalence establishes correspondence between its loop and extracted phases. This theorem does not quantify over arbitrary caller manipulation of private pending values, restoration/persistence entry points, or a caller pausing and resuming an operation with inconsistent external responses. Those require their own API semantics and are not silently included in this trace claim.

The property-transfer theorem supports universal predicates on these finite observations and related final states, including safety properties proved for all finite prefixes. A theorem about raw ideal atomic sends must also be shown valid for the wrapper's withheld failed sends and explicit stutters before being transferred. The theorem does not automatically transfer liveness, infinite executions, hyperproperties, probabilistic bounds, computational security, or erased-memory properties. No model-property hypothesis asserts implementation refinement.

## Validation and review

All proofs were checked incrementally in Lean 4.31.0. The final module gate is `lake.orig build BeaconcryptCore.Refinement.ByteTraceRefinement`. Guarded checks on the execution, property-transfer, and callback theorems report only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; no custom axioms, `sorry`, or `admit` occur. The ratchet workstream independently reviewed the representation and byte-trace interfaces and proofs and found no semantic blocker. Full repository verification and final integration are coordinator responsibilities.
