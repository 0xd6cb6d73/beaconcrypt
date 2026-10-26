# Bounded ProVerif primitive-fidelity checks

This work continues the October 5 handoff on the Rust source of `codex/full-proof-composition` at `0220835d1148afcd695fd0d1429339ca89538bb4`. It does not change the production protocol. The owner approved a separate serial verification group on October 5, keeping the 1,800-second time limit and 10 GiB address-space limit per target. The existing 49-target free-schedule group and its three-hour budget are unchanged.

## Encoding profile

`crypto-fs-encoding.pvl` ports the measured P0 `t1enc` profile. Its X25519 operations accept the existing canonical and high-bit-alias public encodings with equal DH outputs. A low-order symbol produces an all-zero result at the core boundary. Its ML-KEM decapsulation has a correctness case and a deterministic implicit-rejection fallback. The signature, KDF, AEAD and CTX portions are identical to `crypto.pvl`, which the checker verifies after removing comments. The profile uses the same joint Ed25519/X25519 secret names as the existing model; this is a symbolic interface, not a proof from ordinary EUF-CMA.

The high-bit behavior is the functional interface specified by [RFC 7748 section 5](https://www.rfc-editor.org/rfc/rfc7748.html#section-5) and already exercised by `phase2-x25519-alias`. Implicit rejection is the functional behavior of [FIPS 203](https://csrc.nist.gov/pubs/fips/203/final), modeled on admitted ciphertext strings. Neither primitive implementation is proved here. Abstract message decoding remains an external interface contract.

The profile retains role-asymmetric DH, so it does not establish same-role DH equalities or cover every X25519 equivalence class. ML-KEM shared-secret and fallback terms remain free constructors; in particular, the existing cross-public-key binding idealisation is not obtained from IND-CCA. HKDF, AEAD and CTX retain their existing symbolic idealisations. This profile therefore advances F13 without closing the computational/symbolic bridge.

## Exact process changes

`fs-encoding-registration.pvl` is a maintained, reviewable derivative of `fs-registration.pvl`. The checker constructs the expected token sequence by adding exactly three pieces: a four-output nonzero gate between Server DH and root construction; its refusal branch, which emits `FsServerZeroRejected` and `FsServerAcceptFailed` and continues with the exact entry counter and consumed slots; and the same four-output gate after Beacon DH and before root construction. Every other process token must match, including source order, response fields, pin comparison, sequence-one gate and binding check. Tests deliberately remove or relocate a gate, alter its inputs, consume an identifier on failure, and change root, pin and sequence fields; every such drift is rejected.

The Rust core rejects zero in any of `dh1` through `dh4` in `beaconcrypt-core/src/pqxdh.rs:383-389`, before constructing its 192-byte input. Both adapters call this core boundary; their trusted native DH calls can reject earlier. The new zero-retry witness is explicitly a core-boundary witness. It does not say that libsodium returns an all-zero DH value, or that its rejection checks are missing. The public adapter returns `None` on either route. The zero event distinguishes a core failure in this profile from a failed DH destructor and is used only for a witness, never as authentication evidence.

The registration-ID retry witness changes an attacker-signed prekey from a low-order input to a valid input while keeping the identity and one-time key. Because the ID consists of those latter two fields, the second attempt has the same ID. The first attempt is rejected without inserting it, and the second may succeed. This checks the admission boundary rather than assuming a successful transcript.

## Targets and scope

All nine encoding targets use two attempts per Server object, unbounded object/session replication, the original attacker network and the original queries/bound files. Four are security results: A1 (injective registration agreement), A2 (signed-bundle origin with the attacker-owned identity disjunct), R1 (no duplicate acceptance of an ID per object) and R1' (one honest bundle per identity per object). R3, W1, R5 and ZERO-RETRY are reachability witnesses written as expected-false queries. C-NOCHECK is the original consumed-set negative control. The checker requires exact query/verdict text and exactly one reconstructed trace for each false result. Unknown, timeout, resource exhaustion or an unconfirmed trace never passes.

These are additional results at `K_reg = 2`; they do not replace or weaken the original `K_reg = 3` results. They inherit the original registration process's immediate build/drop schedule, fresh registration payloads and honest Beacon pins. The outstanding L1–L5 source-abstraction obligations remain explicit. In particular, these results alone do not cover arbitrary pending-token/build schedules or arbitrary reached record states.

The existing canonical/high-bit exact-response negative control remains the evidence that exact raw-ephemeral agreement is false. This profile does not revive that claim. Same-role DH, the more general KEM-controller authentication interface and active strong secrecy remain separate work.

## Verification

Run `make -C beaconcrypt-core check-proverif-primitive-fidelity` inside the minimal locked proof shell and under the shared ProVerif lock. The target executes the checker tests and the serial profile. It is also a separate step in `verify-in-shell` and `verify-proverif-in-shell`; it is never in the parallel roster or `check-proverif-fs`. `PROVERIF_PRIMITIVE_LOG_DIR` preserves individual logs. The checker disallows larger per-target caps without a code change and review.

The independently reviewed source commit `db1d524aeb5f257e2172f01d59a7a9cd1cb5a5aa` passed the exact-tree Make primitive group: all nine exact results, 221.2 seconds of serial ProVerif time, 25 transcript-fidelity tests and 17 checker regressions. The separate Make inventory gate passed; the unchanged fs checker passed its 61 regressions and cargo formatting passed. The [portable receipt](handover/resume-2026-10-05/primitive-encoding/README.md) retains the input hashes, exact targets and compressed logs. The 49 unchanged existing fs targets were not repeated at this focused stage.
