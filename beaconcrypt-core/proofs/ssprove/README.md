# SSProve computational proof pilot

`CtxEventReduction.v` is a repository-owned feasibility theorem for the computational CTX proof. One execution distribution records both the protocol-misattribution bit and the collision bit extracted by the reduction; the theorem proves in SSProve's probability semantics that the first event's probability is at most the second event's probability, given the deterministic CTX event implication.

The deterministic implication is intentionally a theorem parameter. It is the cross-prover contract intended to be discharged by the existing F* CTX witness plus a reviewed representation bridge; that bridge remains an integration obligation, and this Rocq development does not re-prove implementation correctness.

The pilot does not import hax-generated Rocq or hax's Hacspec library. The pinned hax revision still exports `Hacspec_Lib_Pre.falso : False` through its aggregate library, so generated-code integration is not a trusted build path until that upstream library is repaired or safely isolated and audited.

Run `make verify` in this directory to enter an ephemeral shell built from the repository's locked nixpkgs input, compile the theorem under Rocq 9.0.0 and SSProve 0.2.4, check the exact assumption allowlist, and run `coqchk`. Compiled output is written only below repository `target/formal-verification/ssprove/`.
