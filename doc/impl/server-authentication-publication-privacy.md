# Ordinary privacy endpoint for the publication reference

`PqxdhServerAuthPublicationPrivacy` applies the existing ordinary CTX privacy theorem to the exact before-raw decision from [the reference capture proof](server-authentication-publication-random-capture.md). The decision runs the complete source context and residual samplers, all adaptive known-key work, and the mixed reference callbacks, while privately retaining the actual selected record. Its first selected raw request supplies the candidate bytes and is stopped before any selected opening. The reference's actual optional replies and private component effects are retained.

The canonical ordinary CTX probability is bounded by the IND$ advantage of the constructed prefix-validation reduction, plus `H / 2^128`, plus the IND$ advantage of the constructed ciphertext-view reduction, plus `1 / 2^128`. The final term is the proved unconditional random-tag bound. There is no integrity reduction or raw-alias statistical term, because this observer issues zero selected raw calls. The single-seal nonce-range side condition is discharged numerically. The fallback argument used by the generic privacy theorem disappears with its empty attempt-indexed sum and does not occur in this endpoint.

`validation` and `view` are the actual ordinary reductions for that source-sampled decision. `lossENN` spells out their two advantages and both statistical terms. `loss_finite` proves finiteness before `loss` converts the total to a real number. `source_bound` supplies the full real-valued bound with `H = entryReductionBudget caps qCoin Q qHash qH + 76`; the only operational budgets are the same concrete KEM callback bounds and four original adversary query bounds. There is no caller-supplied first-seal, writer-failure, honesty, freshness, source-origin, or tag-independence premise.

`PqxdhServerAuthPublicationPrivacyResources` proves the exact constructed reductions' oracle bills. With `B0 = H + 64 * (H + 1)`, the ledgers are:

| Experiment | Uniform-query allowance | Encryption-query allowance |
| --- | --- | --- |
| Prefix-validation reduction | `B0` | `2` |
| Ciphertext-view reduction | `B0` | `1` |
| Either complete real IND$ challenger | `32 + B0` | Its reduction's allowance |
| Complete random validation challenger | `B0 + Usize.max + 32` | Its reduction's allowance |
| Complete random view challenger | `B0 + Usize.max + 16` | Its reduction's allowance |

The body-byte allowance is derived from the actual source checked-addition gate, not from the number of API calls. The random challengers pay their actual tags and sample no hidden record key; the real challengers pay their 32-byte key. Local known-key cryptography, codec operations, deterministic validation, and general running time are distinct from these oracle counts. Known-key aliases and real public hashing remain permitted and charged by the inherited compiler.

This is the real/canonical endpoint for the deliberately forced reference, not yet a theorem about actual unpublished source records. The actual failed-publication/reference coupling, ordered occurrence transport through the dynamic known-key interface, and the new accepted-observation R1/key-schedule transport still need to connect that event to this decision. The original B theorem and maintained ProVerif queries remain unchanged. No writer totality, codec injectivity, conditioned tag law, or new primitive contract is assumed.
