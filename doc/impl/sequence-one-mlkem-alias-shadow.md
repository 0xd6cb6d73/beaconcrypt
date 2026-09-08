# Sequence-one ML-KEM public-key alias diagnostic

The current fourteen main queries, ten main controls, eighteen later-registration queries and twenty-nine post-registration queries all retain their reviewed outcomes when an isolated shadow theory removes shared-secret public-key injectivity. This is evidence about these seventy-one symbolic queries. It is not a computational ML-KEM theorem, a proof that all protocol correspondences are independent of that assumption, or a justification for changing the maintained primitive theory.

The experiment uses the sequence-one topic's unchanged production inputs from `e02dcd14bc2a9c5447bdf41a99e8ccff3a95214a`. All new theory, controls, runner outputs and logs are confined to `/tmp/ps1-kem-alias-shadow`. No Rust, existing ProVerif process, existing query, primitive declaration, fidelity matrix, checker or reviewed inventory was edited. The general 53-process/2444-query family and 422/316 fidelity matrices were not rerun for this diagnostic. No mutation run was launched for this proof/model-only work.

## The exact change and its public countercontrol

The shadow preserves the original two-argument `mlkem_shared_secret(public_key, coins)` frontend and adds a public unary constructor plus the equation `mlkem_shared_secret(public_key, coins) = shadow_mlkem_coin_secret(coins)`. It preserves the original ciphertext constructor and correct-key decapsulation equation. A prominent shadow-only comment distinguishes the added equation from the unchanged baseline comment describing public-key binding.

This removes the inference from equal shared-secret terms to equal public keys. It still forces shared-secret equality to imply equal coin terms, preserves injective ciphertext and public-key constructors, and leaves wrong-key or otherwise unmatched symbolic decapsulation undefined. It introduces no ability to re-encapsulate an already known shared secret without knowing the encapsulation coins. These are substantial remaining idealizations.

The separate `public-equality-control.pv` generates two distinct key pairs, publishes both public keys, and uses one publicly known coin term to evaluate both shared secrets. The baseline makes the equality branch unreachable and the disequality branch reachable. The quotient reverses both classifications. Both reachable branches have reconstructed traces. Therefore the fixed quotient changes an ordinary public equality/disequality observation and is not a general trace overapproximation or public experiment equivalence. Its passing protocol queries cannot repair that failure.

## Actual source and adversary interfaces

The honest encapsulation sites in `environment.pvl` use a fresh coin name exactly twice, in adjacent ciphertext and shared-secret calls under the same selected public key. They occur in the ordinary Server, the malicious-owned-identity fixture and the later-registration Server. `GeneralAdmissionServer` has the same one-key, one-fresh-coin pair. The coins themselves are not returned by those sites. The freshness and absence of cross-key reuse are properties of these honest call sites, not restrictions on the adversary's public constructor applications.

All three ML-KEM constructors are public. An adversary can generate its own secret-key term, derive its public key, choose or reuse coin terms, and evaluate ciphertexts and shared secrets under arbitrary available keys. Symbolic decapsulation is also available with a known secret key, and incoming Beacon responses can trigger the honest Beacon's decapsulation path. The model does not turn a native malformed-ciphertext failure or ML-KEM implicit-rejection output into a proved symbolic rejection rule. In particular, the quotient does not discharge the original wrong-key ciphertext restriction.

The native Server verifies the selected signed ML-KEM key and freshness, parses the selected public key, and calls `crypto_kem::mlkem768::encapsulate(&pq_pub).ok()?`. The caller does not supply encapsulation coins. The Beacon parses the received ciphertext and calls `decapsulate` with its retained registration secret key before deriving the root and opening the initial record. The pinned `libsodium-rs` wrapper also exposes deterministic encapsulation from a public key and seed, so the absence of a coin parameter in the protocol adapter does not remove ordinary public evaluation from a computational attacker.

The real algorithm also does not implement the shadow equation: ML-KEM's internal encapsulation derives its secret and encryption randomness from the input randomness together with a hash of the public key. Internal decapsulation returns a secret derived by implicit rejection when its ciphertext check fails; it does not expose that check as a rejection flag. These algorithmic facts establish why the fixed quotient and partial symbolic decapsulation require separate justification. [FIPS 203, Algorithms 17 and 18](https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.203.pdf).

## Ordinary computational boundary

The defensible ordinary endpoint remains `PqxdhKemIndCca.MlKemScheme` and `oneKey_indCCAAdvantage_eq_branchDist`: one actual generated key, one actual honest encapsulation, its public key and ciphertext in the public transcript, and the real or independently sampled uniform 32-byte candidate supplied only to the private continuation. The actual encapsulation sampler and its effects are retained. The public post-challenge decapsulation service blocks exactly the challenge ciphertext and forwards every unequal ciphertext. No public-key injectivity, ciphertext injectivity, shared-secret uniqueness or robustness assumption is part of this generic KEM endpoint. Honest recipient correctness is separately stated; its perfect form remains an explicit assumption of the current bridge.

`PqxdhChallengeSecretRouting` additionally supplies the relevant private continuation discipline: private root requests at the exact challenge ciphertext reuse the same candidate secret, while unequal ciphertexts use ordinary permitted decapsulation. Full stateful equality requires the module's explicit functional-decapsulation equation; an evaluated distribution equality alone cannot discard primitive work. Public evaluation and ciphertext equality must retain their actual byte semantics, including aliases.

A subsequent target-specific symbolic hop could use this ordinary endpoint only after connecting the actual fresh encapsulation and all matching private uses to its challenge, retaining public evaluations, disclosures and every non-target result. That is an additional proof obligation. A global equation forcing all public same-coin evaluations to agree is not such a hop. Nor do the current results remove the separate X25519 representation/alias limitations, establish live schedule security, or justify independent per-owner material labels.

## Completed checks and retained evidence

All runs used the locked `/nix/store/6sshb9zipvahsxadc92m1pp9jny547yx-proverif-2.05/bin/proverif`. Each baseline and shadow run exited zero and passed the unchanged `check-results.awk` at its original scenario name. Their complete checker outputs are byte-identical within each pair, including query identities and expected polarity. Every FALSE result has a reconstructed trace.

| Existing gate | Queries | TRUE | Traced FALSE | Baseline seconds | Shadow seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| Main | 14 | 14 | 0 | 94.42 | 134.77 |
| Main controls | 10 | 6 | 4 | 46.99 | 62.03 |
| Later registration | 18 | 9 | 9 | 6.19 | 11.65 |
| Post-registration ratchet | 29 | 12 | 17 | 21.98 | 40.43 |

Each mode therefore has 41 TRUE and 30 traced FALSE results, with no timeout or unclassified query. The public-equality control adds two classifications per mode, one TRUE and one traced FALSE, with the opposite branch reachable in each theory. An initial punctuation syntax error in that new control was repaired before both completed runs; it was not counted as a result.

The runner is `/tmp/ps1-kem-alias-shadow/run.py` (SHA-256 `2680c2b90f3f94f92ff19f289c1382b20b52a96b35749c6ec583d26b407a85a1`). `inputs.json` records all fifteen unchanged source/checker fingerprints; the final audit rechecked each (`840ddbd671d57c1c79ba634a78d66bdf185016b00728cdf4def7abd80eb41b5d`). The exact shadow theory hash is `2791e86e5e859e90d1f7b87ce532d4904c5dd5db0a9f4a2ddc58b0ec1b0400c6`; the public-equality control hash is `d59d552c549f098d04da992944e2c54d47bfd256f6f942dd69c73b8ceec8bd51`. `summary.json`, `results.json` and `evidence-sha256.json` retain all counts, timings, outputs and log fingerprints. The independent reviewer read the mutation and runner and reconciled all source hashes and seventy-one query results per mode; that review did not rerun the long processes.
