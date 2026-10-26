# HB-98: computational root bound for the generated native execution

The actual HB-97 generated-Beacon execution now reaches its private uniform-root comparison through four constructed reductions. The bound is one joint Ed25519/X25519 weak-EUF advantage, one ordinary ML-KEM IND-CCA advantage, one explicit secret-input Extract-family advantage and one ordinary uniform-key HMAC PRF advantage. It uses the same optional Phase1 writer, generated owner, adaptive selector, source acceptance, native response builder and complete later record/public/reveal program. The selected candidate may be unchanged, changed, attacker-owned or rejected; there is no honest-selected-candidate premise.

This is a bound for the current one-generated-Beacon interface. The current post program has no native Phase2 or additional private-root request, and that fact supplies the one-HMAC cap. Native Phase2, repeated registration, remaining live key-compromise interfaces, evolving input secrecy, global selection and the live symbolic simulation still require composition. Snapshots, persistence, restoration and their consequences are excluded from the active proof by the user's 2026-09-08 scope instruction. Private state retained inside a reduction is not a storage or restore capability.

## Constructed cryptographic hops

`PqxdhGeneratedBeaconKdf.authenticated_family_bound` composes the existing concrete generated-source authentication/KEM theorem with `PqxdhCorrelatedExtractFamily.correlated_advantage_eq`. The family challenger samples one hidden uniform 32-byte ML-KEM secret. Its public messages are exactly four 32-byte DH coordinates; its real answer is the full 64-byte zero-salt Extract at `0xff^32 || dh1 || dh2 || dh3 || dh4 || secret`. The complete input has 192 bytes. Its random comparison reuses one full answer at repeated messages. The winning event is an ordinary final distinguishing bit, not a protocol authentication conclusion. The actual source-to-HMAC functional equation and this additional family-security contract remain explicit; ordinary secret-key HMAC PRF does not establish secret-input Extract pseudorandomness.

`authenticated_uniform_roots_bound` applies the existing ordered Expand hybrids at every original root-query position. Each term names `indexedReduction` into the ordinary uniform-key HMAC game. Cached equal messages reuse the same root, and projecting a private PRK cache does not assume that different PRKs or roots have unequal bytes. Public HKDF evaluations remain the original fixed function. The endpoint is a private family indexed by the actual DH coordinates under one hidden KEM contribution; it is not a global random-table replacement for public HKDF.

`native_root_query_bound` derives at most one private family query from the actual concrete continuation. It retains the complete preparation as local reduction work, then uses the original optional initial coordinates and the native accepted observer's zero additional private-root requests. It does not assume the query count or omit the native builder and later scheduler. `authenticated_native_root_bound` specializes the ordered sum to this derived cap, producing exactly one HMAC term. An extension exposing native Beacon completion must revisit the cap and preserve correlations with any further matching private roots.

The joint-use forgery reduction is the unchanged private source reduction with its existing freshness history, exact three signatures and attached-verification adapter. The KEM secret remains in the ordinary interpreter; public decapsulation blocks the challenge ciphertext, while private matching roots use the same supplied challenge secret. Source generator interchange is justified by the earlier full-continuation evaluated equality. These statements do not replace that equality by a marginal key-distribution argument or transport resource counts through it.

## Source and reduction accounting

`PqxdhGeneratedBeaconKdfBounds.borrowed_uniform_bound` counts the actual identity seed, prekey and one-time generation, public source coins, optional Phase1 writer and complete native selector bill. `borrowed_class_bound` retains every non-uniform CCA class while separately accounting for the writer's coins. The compiler bill remains `Q_selector + U_selector + 64*(S_selector + R_selector + H_selector)`; every forwarded request and every native draw is charged.

`prepare_uniform_bound` adds the actual ephemeral generator, the maximum of the native and ordinary encapsulation allowances, and the complete native continuation on every possible completed branch. `prepare_class_bound` does the same for base and logical-decapsulation requests. `prepare_decapsulation_bound` uses the source ambient-interface exclusion theorem to show that generation and both encapsulation interfaces introduce no logical decapsulation calls: the full preparation retains the original selector cap `qD`. Native optional failures, blocked attempts and attacker-owned selections retain these bounds.

Write `C = 64 + 5*qAux + U_post + 64*(S_post + R_post + H_post)` for the actual native builder and post-schedule allowance. The five auxiliary handlers each retain their supplied bound; the nine native response categories retain their one-call caps. The source preparation allowance is `uPre = 32 + uPrekey + uOneTime + qSource + qWrite + compilerBill + uEphemeral + max(uNative,uTotal) + C`. Its base allowance is `bPre = bPrekey + bOneTime + bSelector + bEphemeral + max(bNative,bTotal)`, and its logical-decapsulation allowance is `qD`.

`native_sampler_bounds` combines these actual preparation bounds with the independently bounded key-generation, encapsulation, base and decapsulation implementations. It derives the complete native post allowance `C`, with zero post base, logical-decapsulation and private-root requests for this current interface. Those zero selective counts do not make native HKDF, AEAD, parsing, serialization or other local computation free. The original source-order uniform ledger from HB-97 remains separate from this reduction ledger.

For the following reduction games, let `Q = qKeygen + uPre + qBase*bPre + qDecap*qD + qEncap + C`. Both preparation and continuation are bounded for every possible reply, so this conservative allowance may include a completed native continuation in the preparation cap and again in the post cap. No branch is undercharged. The source-shaped reduction's sampler costs are established directly from its program, not inferred from a distribution equality.

| Checked game or reduction | Query or uniform allowance |
| --- | --- |
| Source signing | 3 under the original zero-extra-signing restriction |
| Ordinary KEM reduction, before challenge | `uPre` uniform, `bPre` base, `qD` logical decapsulation |
| Ordinary KEM reduction, after challenge | `C` uniform, 0 base, 0 logical decapsulation |
| Extract reduction | `Q` local uniform calls and at most 1 family query |
| Root-valued reduction | `Q` local uniform calls and at most 1 root query |
| Each constructed HMAC reduction | `Q + 64` local uniform calls and at most 1 challenge query |
| Source-shaped KEM comparison | `Q` uniform calls |
| Shared-secret random and native KEM wrappers | `Q + 32` uniform calls |
| Fair ordinary KEM challenger | `Q + 33` uniform calls |
| Real Extract-family challenger | `Q + 32` uniform calls |
| Random Extract-family challenger | `Q + 64` uniform calls |
| Expanded private-root game | `Q + 64` uniform calls |
| Uniform private-root game | `Q + 32` uniform calls |
| Real and random HMAC challengers | `Q + 128` uniform calls |

`reduction_query_ledger` proves the logical Extract/root/HMAC rows. `reduction_sampler_ledger` proves the complete Extract, projected-root and HMAC challenger rows, including sampled keys or answers unused by a completed client. `ordinary_kem_ledger` proves the same KEM reduction's pre/post classes and source/random/native/fair sampling rows. The generic indexed resource bound holds at every index; the actual security theorem needs only index zero. Uniform counts are calls over the specified finite sampling ranges, not entropy bits or a general runtime estimate.

No extra identity/session/record guessing factor is introduced in this one-target result. That does not justify factor one for a replicated global experiment. The global theorem still must construct and count target selection and every live compromise interface. Native record KDF/seal/open/hash/writer counts retain their previously checked source allowances; this root theorem does not declare evolving record materials independent uniform keys.

## Contracts and validation

The fixed primitive implementations are assumed correct and are not proved internally. Attached signature wiring, the explicit Ed25519/X25519 joint-use endpoint, KEM recipient correctness, functional decapsulation, native/ordinary honest-key compatibility, exact source HKDF equations, the additional Extract-family game and ordinary HMAC PRF remain distinct contracts. Native optional codec/allocator behavior, compiler/runtime correctness, source representation and physical erasure retain their documented scope. The CTX interpretation retains its explicit classical random-oracle idealization; it is not inferred from collision resistance. This stage adds no storage or restore premise.

The two modules contain 13 statements. All direct checks and actual standard-axiom dependency reports pass, and the complete guarded Lean gate passes all 3,357 jobs. The reviewed inventory gate passes all 471 entries. Independent reviewers approved the reduction statements, source interfaces, query ledgers, final inventory and live-state scope. Publication rechecks the exact integrated tree and compares local, fetched and direct private-remote hashes. No Rust or ProVerif source change is included, and mutation testing is omitted under the user's proof-only policy. The main proof continues with the live native Phase2, evolving-key and symbolic boundaries.
