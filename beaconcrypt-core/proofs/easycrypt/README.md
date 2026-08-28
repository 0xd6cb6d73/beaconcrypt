<!-- SPDX-License-Identifier: 0BSD -->

# EasyCrypt computational games

EasyCrypt is beaconcrypt's primary computational-game infrastructure. The checked tree has reviewed coverage counterparts for 30 selected bounded SSProve capstone areas while requiring materially less stateful-oracle and separation boilerplate. This comparison assigns zero value to migration cost and prior work. SSProve remains an independent Rocq/coqchk-rechecked cross-check; ProVerif remains the symbolic regression layer; Lean and F* remain responsible for deterministic implementation correctness and refinement.

Reviewed capstone coverage is neither cross-assistant proposition equivalence nor a production proof. The manifest gate verifies exact declaration heads, reviewed relation labels, and scope text; it cannot compare the meaning of propositions in two proof assistants. These files use finite atoms, idealized primitives, explicit fuel, and restricted protocol state. They do not prove production-width security, primitive security, arbitrary multi-session execution, production receive/cache/rollback/persistence behavior, or QPT/QROM security. No EasyCrypt source in this directory is hax-extracted.

For the functional meaning of these results without proof-system terminology, see [what the computational proofs mean in application terms](../../../doc/formal-verification-analysis.md#what-the-computational-proofs-mean-in-application-terms).

## Modules and capstones

- `Common.ec` defines active/passive and classical/quantum capability labels without adding quantum semantics.
- `ProtocolGames.ec` provides session-indexed mutable-state and active/passive API scaffolding. Its receive transition, corruption model, scheduling, and session abstractions are not production-complete.
- `PqxdhGames.ec` and `PqxdhHybrid.ec` contain bounded scenario and hybrid games, including positive zero-gap controls and the active-quantum advantage-one negative control.
- `ProtocolRom.ec`, `AdaptiveRom.ec`, and `HybridAdaptiveRom.ec` provide fuel-bounded adaptive classical-ROM interpreters, exact trace/count invariants, identical-until-bad simulations, and bad-query probability bounds. `adaptive_rom_advantage_bad_query_bound` is the generic protocol capstone; the scenario lemmas include passive-quantum labels only under an explicitly classical-query interface.
- `RatchetForward.ec` proves the exact erased-message-key distributional equality. `RatchetAdaptiveRom.ec` proves `ratchet_adaptive_advantage_hidden_query_bound` for an arbitrary lossless adaptive classical-ROM adversary.
- `Ctx.ec` proves the modified-CTX pointwise binding-to-collision reduction. AEAD opening is a pure function of exactly `K`, `N`, `AD`, `C`, and `T`; the CTX transcript is formed from `K`, `N`, `AD`, `T`, sequence, and sender, and does not include ciphertext or plaintext.
- `CtxRom.ec` proves bounded CTX extraction, trace, mismatch, and probability-lift lemmas.
- `CtxAdaptiveFullRom.ec` is the full bounded CTX privacy model. Its query type has all six Boolean coordinates `(K,N,AD,T,sequence,sender)`, so the adversary can query every point of the 64-entry abstraction rather than only a fixed-public-field slice. It proves `ctx_full_trace_count_bad_exact`, `ctx_full_programmed_ideal_identical_until_bad`, `ctx_full_true_programmed_distribution`, and the hidden-uniform-key end-to-end classical-ROM capstone `ctx_hidden_uniform_key_true_real_privacy_bound`.
- `RecordIntegrity.ec` contains the bounded integrity classification, collision reductions, trace bounds, and one-bit fresh-tag result.
- `ActiveQuantum.ec` proves the modeled substitution result under named classical-secret recovery capabilities; it does not verify Shor's algorithm or execute the production protocol.
- `ProbabilityBounds.ec` contains reusable probability algebra used by the game hops.

## Trust and assumptions

`check-policy.sh` rejects every unallowlisted axiom and compares each complete normalized declaration with `expected-assumptions.txt`. The current inventory contains exactly seven assumptions:

- `assumption_ctx_encoding_is_injective`, the pending representation/refinement contract connecting the abstract six-field CTX encoder to the concrete 229-byte production encoding.
- `assumption_quantum_recovers_ed25519` and `assumption_quantum_recovers_x25519`, used only as active-quantum attacker capabilities.
- `assumption_adaptive_adversary_run_lossless`, `assumption_hybrid_adversary_run_lossless`, `assumption_ratchet_adversary_run_lossless`, and `assumption_ctx_full_adversary_run_lossless`, which require the corresponding abstract adversaries to terminate when their oracle terminates.

There are no assumptions asserting secrecy, CTX binding, CTX privacy, integrity, distributional equivalence, or an advantage bound.

`implementation-contracts.tsv` records two pending reviewed cross-prover bridges. The CTX row maps Rust `build_commitment_transcript` through hax-generated F* and its injectivity/collision lemmas to `assumption_ctx_encoding_is_injective`. The ratchet row maps Rust `advance_send` through generated Lean and `advance_send_refines` to the abstract EasyCrypt send transition. Both remain pending; the manifest is an auditable trust-boundary ledger and does not make the EasyCrypt games extracted implementation proofs.

## Scope of the result

The completed coverage gate concerns bounded classical computational games. The CTX privacy capstone proves that, in the six-Boolean-coordinate fuel-bounded classical ROM, the true-real versus fresh-ideal decision gap is at most the probability that the ideal accepted trace queries the exact hidden transcript. It must still be composed with production-width AEAD and protocol reductions and connected through the reviewed representation bridge.

The active-classical and passive-classical production theorems remain open. The production skipped-key cache, receive-gap handling, replay behavior, rollback and persistence, concurrency and adversarial scheduling, evolving ratchet compromise, challenge restrictions, and exact multi-user reduction losses are not modeled here. Primitive correctness is delegated to Lean/F*, while primitive computational security must be introduced as explicit assumptions in later reductions.

Mainline EasyCrypt is classical. A scenario named passive quantum but restricted to classical oracle calls is not a QPT or QROM theorem. Neither this tree nor the SSProve cross-check establishes positive passive-quantum security. That result requires an independently pinned and audited quantum framework or lifting theorem plus QPT/QROM primitive assumptions.

## Checking

The locked environment pins EasyCrypt 2025.08, Why3 1.8.2, and CVC5 1.2.1. Run:

```sh
make -C beaconcrypt-core verify-easycrypt
make -C beaconcrypt-core check-inventory
make -C beaconcrypt-core verify
```

The focused parent target reuses the shared locked proof profile, creates a temporary Why3 configuration, requires CVC5, compiles every source with `easycrypt compile -no-eco -p CVC5`, and checks the assumption and implementation-contract policies. Invoke the local `make -C beaconcrypt-core/proofs/easycrypt check` target only from an already entered proof shell. Shared proof profiles are garbage-collection roots; retire an obsolete profile only after every coordinator and agent using it has stopped, then run `nix-collect-garbage` as described in the core proof workflow.
