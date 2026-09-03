<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification

Lean verifies the complete default `beaconcrypt-core` extraction and its refinements to the existing ideal PQXDH and symmetric-ratchet models. The extraction uses Hax, Charon, and Aeneas. ProVerif and SSProve provide complementary symbolic and finite probabilistic results. Concrete primitive implementations, adapters, codecs, persistence, and compiler correspondence remain outside the extracted-core proof.

For detailed explanations and assumptions, see [What the proofs establish](formal-verification-analysis.md) and the [reviewed trust boundary](../beaconcrypt-core/proofs/trusted-boundary.md). The earlier staged plan and historical F* milestone descriptions are preserved in the [design history](impl/formal-verification-design-history.md).

## Checked core guarantees

| Area | Checked result | Main Lean evidence |
| --- | --- | --- |
| Panic freedom | Every one of the 269 extracted non-helper `RustM` operations returns `ok` on every represented input, without a validity or successful-response premise. Explicit protocol errors remain permitted results. | `PanicFreedom.API` and the signature-derived coverage gate |
| Exact bytes and control | Tagged-key encodings, KDF partitions, PQXDH and commitment transcripts, checked counters, bounded lookup, key consumption, and restoration guards. | `PqxdhSurface`, `RatchetByteSurface`, `RatchetControlSurface`, `CommitmentSurface` |
| Receive structure | Every valid receive completes, preserves structural validity, and classifies plaintext by its actual trace, prepared target, callback result, and publication. Failure restores the entire entry. | `RatchetReceiveStructural`, `RatchetReceiveRollback`, `RatchetCachedPreparation`, `RatchetRelativeFuture` |
| Replay and retry | Successful targets cannot be consumed again; arbitrary later callbacks/interpreters cannot revive them. Repeated rejected operations leave an arbitrary retry equal to direct execution and preserve capacity. | `receiveNext_success_replay`, `SuccessfulReceive.consumes`, `retry_after_rejection_eq_direct` |
| Future keys | Exact relative KDF order and material, unchanged old key prefix, bounded skipped-key publication, and target exclusion. Fifty derivations publish forty-nine skipped keys; the maximum current admitted gap is fifty-one derivations with fifty retained keys. | `RatchetRelativeFuture`, `RatchetFutureSurface`, `RatchetReceiveStructural` |
| Canonical lifetimes | Complete sends and receives preserve canonical chain/material provenance through arbitrary finite mixed histories; ideal decryption callbacks give exact ideal receive correspondence for positive wire targets. | `RatchetRoleReachability`, `RatchetReceiveIdeal`, `RatchetLifetime` |
| Restoration | Arbitrary generic structural states restore atomically; trusted canonical persisted chains and material preserve provenance. Structural validity alone does not authenticate a snapshot. | `RatchetRestoreStructural`, `RatchetRestoreSurface`, `RatchetRestoreProvenance`, `RatchetMaterialRestore` |
| PQXDH sessions | Exact deterministic registration, authenticated assigned-ID binding, complementary initial kernels, and complete bidirectional concrete session lifetimes under fixed interpreters and stated input agreement. | `PqxdhProtocol`, `PqxdhConcreteSession`, `PqxdhSessionLifecycle` |
| Commitment | Exact 229-byte production transcript, injective field encoding, and a constructive hash-collision witness for distinct accepted openings. | `CommitmentSurface`, `PqxdhCommitmentRefinement` |

These guarantees concern the current first-order production phases, including their complete synchronous Lean drivers. The Rust adapter follows that phase interface, but its source-to-driver correspondence and primitive response fidelity remain external obligations. The ideal models themselves are unchanged by the Lean proof work.

## Other verification layers

ProVerif checks the maintained active-classical, passive-classical, passive-quantum capability, compromise, receive-rejection/capacity, identity-binding, and negative-control scenarios. Its network and cryptographic operations are symbolic. Its finite record schedules do not replace the universal extracted-core receive proofs.

The Lean computational development gives the documented CTX and PQXDH reductions under explicit primitive-game and query-accounting assumptions. SSProve independently checks finite ROM, binding, privacy, and protocol games. Neither proves the security or correctness of the concrete primitive libraries, and the documented production-width, adapter, cross-prover, and broader computational-composition gaps remain.

## Reproducible checks

Run the locked aggregate verification and the separate trust-boundary inventory from the repository root:

```bash
make -C beaconcrypt-core verify
make -C beaconcrypt-core check-inventory
```

`verify-lean` checks the extraction and complete Lean project independently. `check-generated-lean` additionally rejects drift in the generated extraction. `check-lean-panic-freedom` reconstructs unconditional theorem signatures for every extracted operation and rejects missing or stale coverage; `check-lean` compiles those certificates and every handwritten module. The root module and all-module Lake glob are guarded. Repository-owned Lean files cannot contain unfinished proofs or custom axioms.

The reviewed inventory hashes the complete monitored source, generated, proof, control, and validation file sets. Its digest updates require review of the changed artifacts. After the final Nix verification, run `nix-collect-garbage` only when no other repository Nix build or shell is active.

## Historical F* correspondence

The migration inventories every historical lemma declaration: [192 ratchet declarations](impl/ratchet-fstar-coverage.md), [68 PQXDH declarations](impl/pqxdh-fstar-coverage.md), and [25 commitment declarations](impl/commitment-fstar-coverage.md). These ledgers distinguish semantic matches from removed implementation helpers. Five old planner bounds changed during the earlier extraction refactor: the current implementation retains fifty skipped keys and derives the authentication target separately, allowing fifty-one total derivations. The old fifty-total-derivation clauses are explicitly adapted, not claimed as literal statement equality.

The archived F* sources describe the predecessor callback implementation and remain available in Git history. The migration progress and completed verification checkpoints are recorded in the [Lean proof completion record](impl/lean-proof-completion.md).
