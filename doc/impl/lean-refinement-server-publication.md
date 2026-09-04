# Server candidate publication refinement

This workstream composes the extracted candidate-bound initialization, first-send phases, and candidate commit or abort with the explicitly named optional-publication closure of `Pqxdh.serverEmit`. It does not claim that a failed concrete seal refines a completed atomic `serverRespond`: on a free identifier, that ideal operation increments the allocation counter while concrete failure retains the previous counter. The existing strict atomic counterexample remains part of the result.

The candidate relation must be derived from actual extracted preparation and preserve previous and next counters, assigned identifier, both identities, server sender identifier, ephemeral key, KEM ciphertext, and associated data. The success theorem must preserve the complete emitted response, published peer, and advanced full byte-kernel relation. The failure theorem must execute actual first sealing and abort, returning the previous allocation state without a peer or response. The peer map and consumed-registration set belong to external context; failure leaves that context unchanged at the already-consumed registration prefix, while success prescribes inserting the exact peer output. This prescribes an adapter boundary contract and does not verify an adapter implementation.

## Milestone ledger

- Reviewed and proved previously: `finishCandidate_failed`, exact atomic-counter mismatch, and explicit ideal optional-publication closure.
- Newly proved: `prepare_candidate_refines` derives every candidate field from extracted preparation; `finish_candidate_refines` covers success and seal failure; `prepareAndFinish_refines` composes actual preparation, initialization, first sealing, and commit or abort for every fixed-binding allocation outcome. `prepare_binding_changed` separately proves the exact changed-binding admission abort.
- Validated milestone: the complete module checks without diagnostics under pinned Lean 4.31.0; all prerequisite builds succeeded.
- In progress: lifting from Boolean seal outcomes to arbitrary boundary-compliant callbacks and deriving the supplied root from the actual accepted transcript under `RootKdfLaw`.
- Boundary assumptions: root and initial/ongoing KDF primitive contracts, record sealing/opening interpretation, correct allocation availability and unchanged pinned binding during admitted preparation, and externally owned replay/peer context.
- Strict atomic refinement with failed sealing remains impossible under the unchanged ideal operation; transferable properties must be shown stable under optional publication and abort.
