# Pre-seal-chain reveal negative control

`PqxdhServerAuthPresealControl` tests why the original registration reveal returns the advanced installed kernel. Its separate handler records the exact KDF input used by the first Server send and changes only the returned copy of a revealed kernel: the copy's send chain is replaced by that recorded chain₀. The actual installed kernel, consumed token, peer map, counters and caches are never rolled back. The original `PqxdhServerAuthExperiment.authHandler` is unchanged.

## A source-observed chain

`tail_erase`, `program_erase` and `program_queries` show that recording the reached KDF requests preserves the complete original callback/program and its probabilistic query bill after erasing just the new private list. Optional seal, frame and outer writer failures remain in that program. `tail_history`, `tail_kdf` and `tail_aux` characterize each observed source callback, including its actual fixed-HKDF response and the unchanged stateless auxiliary outcomes.

`send_seal_history` proves that sealing does not alter the saved KDF list. `send_history` derives the exact old send-chain request and production domain label from the extracted nonexhausted sender. `after_history` retains that request through plaintext erasure and both optional publication branches. `after_peer` derives the installed peer at the returned response key ID from successful outer publication. `build_history_peer` consumes the actual initializer and every original admission branch: a successful build recorded exactly one request for the source initializer's old send chain and installed a peer under its returned ID.

The control's `build` runs this observed builder once. `built_reveal` connects its successful response to a present revealed kernel whose send chain is that exact source chain. No desired plaintext, root-derived substitute or assumed chain equality is inserted into the adversary's input. `build_erase` preserves the original complete build program, including full Server state, pending-token consumption, original successful-seal history and CTX cache. `forward_erase` does the same for all capabilities that the control forwards unchanged.

## Concrete attack and original receive path

The adversary parses the actual published Phase1, relays it to one Server accept, requests a build with `payload`, and reveals the returned key ID. It computes the real source ratchet step on the altered revealed send chain. It then seals `LE64 keyId ++ other`, with the pinned public associated data, public ephemeral and KEM ciphertext from the original response, and a commitment obtained from the same public BLAKE2b oracle. It writes the actual abstract frame and Phase2 interfaces and delivers the resulting bytes to the unchanged Beacon finish. `other` is an adversary-chosen nonempty application payload distinct from `payload`.

`run_bind`, `run_pure`, `run_query` and `forward_run` retain complete evaluated continuations and both source and family states. `run_build`, `run_reveal`, `run_accept`, `run_hash` and `run_finish` connect the concrete control to the original operations: the altered reveal is deterministic and preserves all state; the public hash uses the same shared cache; the finish still returns the original optional plaintext and performs the original registration checks.

`reseal_wins` applies the existing source seal/open correctness and exact Beacon finish to the replacement message. It derives an actual acceptance snapshot containing the original partner session and its earlier successful seal. The accepted payload differs from that seal's application payload, so the original W2 event holds. `after_accept_wins` supplies the old-chain and peer facts from the real observed build and reveal. Its source publication-liveness condition is discharged in `pair_failure` using the accepting checks and existing bounded-writer theorem; it is not a premise of the final result.

## Probability and query accounting

`pair_failure` proves that, for each actual sampled KEM pair, failure of this concrete attack is bounded by that pair's ordinary decapsulation-correctness error. `controlBody_run` keeps the original R1 constructor schedule, actual Phase1 publication and full final state. `failure_bound` averages the pair result over that unchanged joint sampler. `preseal_control` therefore proves:

```text
Pr[W2 in the separate pre-seal-reveal experiment] ≥ 1 − kemError(setup).
```

`presealGame_event` uses the original authentication-winning event in the Boolean control game, and `preseal_reveal_control` gives the same lower bound for that game because W2 implies Win. The coefficient of the KEM correctness term is one. There is no target-selection loss, guessed independence, collision term or cryptographic hardness premise in this negative control.

The final hypotheses are the existing `ControlLaws` and functional decapsulation contract, `acceptAll` checks, two distinct nonempty payloads, an original payload fitting the source allocation, both protected payloads fitting the bounded writers, and a Server key ID below the maximum. They supply functional liveness, not authentication. The theorem derives the actual pending token, successful publication, saved chain, partner and winning event. The existing functional KEM contract includes complete effect-free decapsulation as specified by this experiment; primitive implementation correctness remains external.

`adversary_budget`, `adversary_classes` and `adversary_total` count every optional reply branch:

| Public API request | Maximum |
| --- | ---: |
| Accept | 1 |
| Build | 1 |
| Reveal | 1 |
| Commitment hash | 1 |
| Beacon finish | 1 |
| Public HMAC | 0 |
| Explicit adversary uniform coins | 0 |
| Total API requests | 5 |

These are API bounds, not a claim that the complete experiment draws no coins or performs no primitive work. In particular, the zero public HMAC count does not remove local KDF work: `reseal` performs at most one real 76-byte ratchet-step evaluation and one local AEAD seal, then sends at most one public commitment-hash request. All original identity/scalar/KEM sampling, source callbacks, real public KDF computations, local attacker ratchet derivation and AEAD sealing, codecs and the shared hash interpreter remain in the concrete programs. The exact source/program erasure lemmas show that the observation adds no probabilistic query. The ordinary source resource ledger remains the accounting for that retained work.

## Scope

This is an intentionally altered reveal experiment. It does not establish an attack on the unchanged protocol, whose original reveal exposes the installed advanced chain. It shows that exposing the erased initial chain would invalidate the intended authentication event, so the reveal boundary is tested by a live control rather than a vacuous rejection model.

The original restricted programmable Extract ROM, shared CTX/BLAKE2b ROM, joint identity/DH wiring and abstract codec contracts remain unchanged. The constructor order here is the original R1 experiment order; the separately checked native-source bridge justifies the production constructor order with complete evaluated-continuation interchange. No primitive implementation, native serializer, snapshot or persistence behavior is proved or modeled by this control. Joint-witness instantiation and the full adaptive selected CTX authentication reduction are separate consumers.
