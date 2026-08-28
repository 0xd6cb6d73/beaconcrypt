<!-- SPDX-License-Identifier: 0BSD -->

# EasyCrypt computational-security proof decision

## Decision

EasyCrypt is the primary infrastructure for beaconcrypt's computational games. This decision assigns zero value to migration cost, existing SSProve work, and existing CI. It follows from compiler-checked coverage of 30 selected bounded capstone areas together with EasyCrypt's materially smaller proof-state and stateful-oracle burden. SSProve remains an independent Rocq/coqchk-rechecked cross-check for related bounded abstractions; it is not the primary authoring path. ProVerif remains the symbolic regression and attack-discovery layer, while Lean and F* remain responsible for deterministic implementation correctness and refinement contracts.

The coverage gate is deliberately narrow. It means that EasyCrypt now has checked counterparts in 30 selected bounded finite-game areas represented in the SSProve tree. The gate checks exact declaration heads and reviewed relation metadata but cannot mechanically establish proposition equivalence across proof assistants. It does not mean that either tree proves production beaconcrypt end to end. Neither development currently supplies production-width reductions, an arbitrary multi-session protocol proof, the production receive/cache/rollback/persistence state machine, primitive-security reductions, or QPT/QROM security.

## Why EasyCrypt is primary

The comparison excludes sunk cost. Both systems can express the bounded classical games, but the completed coverage exercise shows that EasyCrypt's imperative modules, mutable procedures, adversary functors, pHL/pRHL judgments, and relational `call` rules express beaconcrypt's stateful games with less package plumbing and fewer separation/interface obligations. That difference is material for ratchets, bounded adaptive random oracles, query traces, bad-event invariants, and active/passive API restrictions, all of which are expected to change with the protocol.

SSProve's important intrinsic advantage is that Rocq produces proof terms that `coqchk` can recheck. EasyCrypt instead checks scripts in its proof engine and discharges generated obligations through the pinned Why3/CVC5 stack. This is why the SSProve tree remains valuable as an independent kernel-rechecked cross-check. That audit advantage does not outweigh EasyCrypt's lower stateful proof and maintenance burden for the primary development now that the selected bounded-capstone coverage gate has passed.

No prover receives implementation-extraction credit. Direct hax-to-EasyCrypt extraction is not used, and the direct hax/Rocq route is not trusted as a bridge. The proof architecture uses small, explicit Lean/F*-to-game representation contracts whose review status is recorded in `proofs/easycrypt/implementation-contracts.tsv`.

## Checked bounded theorem surface

The EasyCrypt tree currently checks the following bounded abstractions:

For a developer-oriented explanation of what these results mean functionally, see [what the computational proofs mean in application terms](../formal-verification-analysis.md#what-the-computational-proofs-mean-in-application-terms).

- `Common.ec` defines the four attacker capability labels. These labels classify modeled capabilities; they do not add quantum semantics to EasyCrypt.
- `ProtocolGames.ec` defines session-indexed mutable state, first-writer-wins registration, a bounded send transition, passive and active API views, and adversary-parameterized games. It is scaffolding rather than a production protocol reduction.
- `PqxdhGames.ec` proves the bounded positive zero-gap results and the capability-level active-quantum advantage-one control. `PqxdhHybrid.ec` provides the one-hidden-component hybrid statements.
- `ProtocolRom.ec` and `AdaptiveRom.ec` provide domain separation, query-count and trace consistency, an arbitrary lossless stateful classical-ROM adversary, identical-until-bad simulation, the bad-query advantage bound `adaptive_rom_advantage_bad_query_bound`, and the active-classical, passive-classical, and passive-quantum-with-classical-query scenario corollaries. The last label is not a QPT/QROM result.
- `HybridAdaptiveRom.ec` proves the adaptive one-hidden-component classical-ROM bound and corresponding scenario specializations. It retains all five hybrid components in the query type and exposes the exact hidden-component query event.
- `RatchetForward.ec` proves exact distributional equality after erasing the message-key coordinate. `RatchetAdaptiveRom.ec` proves the fuel-bounded adaptive classical-ROM ratchet bad-query capstone `ratchet_adaptive_advantage_hidden_query_bound` with exact trace and count invariants.
- `Ctx.ec` proves the pointwise modified-CTX binding reduction from two distinct accepted explanations of one protected payload to a collision, conditional only on the reviewed encoding-injectivity bridge. `CtxRom.ec` supplies the bounded CTX extractor, trace bound, and probability lifts.
- `CtxAdaptiveFullRom.ec` uses the full six-Boolean query `(K,N,AD,T,sequence,sender)`, permits queries at every one of the 64 bounded transcript points, records every accepted query, and proves exact trace/count/bad invariants. It proves programmed-real versus fresh-ideal identical-until-bad, true-real versus programmed-real distributional equality, and the hidden-uniform-key classical-ROM bound `ctx_hidden_uniform_key_true_real_privacy_bound` inside this 64-point game. This is the CTX bounded-coverage capstone, not a production-width or QROM theorem.
- `RecordIntegrity.ec` proves the bounded query-or-guess classification, cross-context and cross-sequence collision reductions, trace bounds, and the one-bit fresh-tag probability result.
- `ActiveQuantum.ec` proves a capability-level bundle-substitution acceptance result under explicit Ed25519 and X25519 recovery contracts. It neither verifies quantum algorithms nor proves a production beaconcrypt attack execution.

The EasyCrypt and SSProve developments cover related conclusions only at this bounded abstraction level, and several mapped propositions use materially different game interfaces. Boolean atoms, finite tables, explicit fuel, idealized primitives, and restricted state are intentional proof-model choices. Source-line counts are not security evidence, but the successful coverage exercise is relevant engineering evidence: the EasyCrypt counterparts reached the selected bounded areas without reproducing SSProve's state-separation and package-validity boilerplate.

## Assumption and trust audit

`proofs/easycrypt/check-policy.sh` rejects unallowlisted axiom declarations and fingerprints complete normalized declarations against `expected-assumptions.txt`. The checked inventory currently contains exactly seven assumptions:

- `assumption_ctx_encoding_is_injective` states that the abstract six-field CTX encoder is injective. It is the pending representation bridge for the production transcript `K || N || AD || T || LE64(sequence) || LE64(sender_id)`.
- `assumption_quantum_recovers_ed25519` and `assumption_quantum_recovers_x25519` are explicit capabilities used only by the active-quantum negative control.
- `assumption_adaptive_adversary_run_lossless`, `assumption_hybrid_adversary_run_lossless`, `assumption_ratchet_adversary_run_lossless`, and `assumption_ctx_full_adversary_run_lossless` restrict the respective abstract adversaries to terminating probabilistic computations when their oracle terminates.

No assumption states protocol secrecy, CTX binding or privacy, ciphertext integrity, a bad-query bound, distributional equality, or the desired conclusion. Primitive correctness and primitive computational security are outside these bounded game proofs and must enter later compositions as explicit contracts.

The implementation contract manifest has two pending reviewed cross-prover bridges. The CTX row maps Rust `build_commitment_transcript` through hax-generated F* and `production_commitment_input_is_injective;ctx_distinct_openings_imply_hash_collision` to `assumption_ctx_encoding_is_injective`. The ratchet row maps Rust `advance_send` through generated Lean and `advance_send_refines` to the abstract EasyCrypt send transition. These rows are a trust-boundary ledger, not certificate transfer, and neither is marked complete. No document should describe an EasyCrypt game as hax-extracted.

## Remaining proof work

The primary EasyCrypt path still needs production-shaped games and reductions. The active-classical target must model bounded but parameterized sessions and records, adversarial scheduling, replay and receive state, compromise timing, challenge exclusions, failure leakage, and scoped forward secrecy, then reduce its advantage to explicit multi-user signature, KEM, DH, combiner, KDF, AEAD, and CTX assumptions. Passive classical security should follow by interface restriction.

CTX binding must be connected to the reviewed production representation bridge. CTX privacy must compose the checked hidden-input classical-ROM hop with an AEAD confidentiality reduction at production widths. Ordinary record integrity must retain a base-AEAD forgery term for modified ciphertext or tag bytes and use the CTX collision branch only for distinct semantic explanations of an unchanged protected payload.

Neither EasyCrypt nor SSProve currently proves passive security against arbitrary quantum polynomial-time adversaries or quantum random-oracle queries. The passive-quantum classical-query lemmas are useful dependency controls only. A positive passive-quantum result requires a separately pinned and audited quantum framework or a justified lifting theorem, QPT-secure primitive assumptions, and a QROM treatment of the secret-key-containing CTX input. The active-quantum result remains a negative capability theorem under the named recovery contracts.

## Reproducible checks

The repository pins EasyCrypt 2025.08, Why3 1.8.2, and CVC5 1.2.1. From the repository root, the supported checks are:

```sh
make -C beaconcrypt-core/proofs/easycrypt check
make -C beaconcrypt-core check-inventory
make -C beaconcrypt-core verify
```

The first command creates a temporary Why3 configuration, compiles every listed EasyCrypt source with `easycrypt compile -no-eco -p CVC5`, and runs the assumption and contract policy. The parent verification target runs the locked proof environment. After the final Nix-backed verification completes and no other repository Nix process is active, run `nix-collect-garbage` as required by the repository workflow.

Completion of the overall computational proof requires more than this bounded coverage milestone: production-relevant game refinement, reviewed Lean/F* bridges, primitive reductions with exact advantage accounting, production state and multi-session coverage, and a separately qualified quantum result remain open.
