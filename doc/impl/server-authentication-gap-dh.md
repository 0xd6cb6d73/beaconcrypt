# Server-authentication Extract-query reduction (B6)

`BeaconcryptCore/Computational/PqxdhServerAuthGapDh.lean` establishes the BadB term in the approved server-authentication experiment. BadB means that an adversary's public zero-salt HMAC query contains the exact 192-byte input used by the target Beacon's root derivation. The theorem `badB_le_gapDh` bounds its probability by the success probability of the concrete reduction `PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH)`, with coefficient one. The same reduction appears in the resource theorems. There is no candidate-guessing or session-selection multiplier in this hop.

This is the experiment's approved R1 idealization: only zero-salt HKDF-Extract on 192-byte inputs uses a shared programmable classical random oracle. Every other HMAC evaluation, including root Expand, stays real. The reduction uses the existing `PqxdhJointGapDh.game` with the source joint identity distribution and its twist-inclusive decision services. Its functional premise is `X25519ClassLaw`; the remaining functional wiring and public rejection domains are exactly those already carried by `PqxdhServerAuthExperiment.Setup`. It introduces no new primitive contract. In particular, it does not use ML-KEM correctness or IND-CCA, Ed25519 weak-EUF, scalar spread, nonzero-honest-DH, a codec read-back law, or a presumed authentication conclusion.

## How the reduction works

The scanning client receives the challenge Server identity public key and Beacon prekey public key, then runs the existing experiment body with no revealed Server seed. The locally sampled Beacon identity, one-time key and KEM pair, the exact Phase 1 program, arbitrary Server accept/build calls, one-shot Beacon finish, public HMAC and BLAKE2b queries, and post-registration state reveals remain in that body. The executable table interpreter takes neither challenge secret as an argument.

The private table stores concrete adversary query bytes or the public-coordinate description of an honest root request. It compares concrete keys directly. Comparing bytes with a root description uses one or two decision queries. Comparing descriptions uses the approved X25519 class law and, where needed, one decision query for the mixed known/selected third DH coordinate. Rejected DH requests are decided by the existing public rejection domains, are logged, and create no entry. Equal concrete input bytes always reuse the first table entry, including encoding aliases and correlations between honest and adversarial requests.

`service_fst`, `sym_step` and `sym_complete` prove exact simulation after answering the decision service with the challenger's secrets and concretizing the private table. This preserves the whole computation's return value and complete family history, without a marginal-distribution argument or an initial table-uniqueness premise. The executable scan client and table interpreter require no challenge-secret argument; this is not a separate nonexposure theorem for arbitrary functional setup instances. The mathematical concretization is used only to compare the two experiments.

`honest_no_rom_public` proves that honest work does not insert an adversary-style table-domain HMAC query. `touches_history` then identifies the ordered adversary-touch subsequence of the actual experiment with the public table-query subsequence of the family history. `candidates_length` shows that a vector of length `qH` retains all DH1 coordinates of those queries. If BadB occurs, `badB_candidate` uses the existing Beacon-origin invariant to show that one retained coordinate is precisely the nonzero challenge cross DH value. `candHit_eq_gapDh` combines exact simulation with the existing candidate scanner. These statements give `badB_le_gapDh` directly.

## Query accounting

Let `qH` bound the adversary's table-domain HMAC queries and let `Q` bound every Server accept request, including rejected requests. Let `u` be an explicit bound on all uniform queries of `PqxdhServerAuthExperiment.body setup codec checks adversary none publicValue`, for every required public challenge. This is a resource premise on the actual complete body: it includes Beacon identity and one-time generation, KEM key generation and encapsulation/decapsulation through their fixed base interpretation, Server ephemeral generation, CTX random-oracle sampling, Phase 1 work and adversary coins. B6 leaves that resource parameter explicit. The later [complete source-resource proof](server-authentication-source-resources.md) now discharges it for the same literal body from ordinary primitive/base caps and the adversary coin, accept and public-hash budgets; it also expands the exact same extractor and challenger bill. No primitive or ambient work is declared free.

| Quantity | Checked bound | Theorems |
| --- | --- | --- |
| Source challenge-signing requests | 0 | `body_sign` |
| Source public Extract-table requests | `qH` | `body_table` |
| Source root derives | `Q + 1` | `body_derive` |
| Scanning-client signing requests | 0 | `scanClient_signing` |
| Scanning-client decisions | `2*qH*(Q+1) + 2*(Q+1)*(qH+Q+1)` | `scanClient_decisions` |
| Complete extractor decisions | `2*qH*(Q+1) + 2*(Q+1)*(qH+Q+1) + qH` | `extractor_resources` |
| Complete extractor uniform draws | `u + 64*(qH+Q+1)` | `scanClient_uniform`, `extractor_resources` |
| Ordinary Gap-DH game uniform draws | `64 + u + 64*(qH+Q+1)` | `extractor_game_uniform` |

The source signature cap is zero because the honest Phase 1 signs using the locally generated Beacon seed; it never asks for a signature under the hidden Server seed. The derive cap uses one request per Server accept and a checked potential for the target Beacon's single-shot finish. The final candidate scanner adds at most `qH` decisions and no signing or uniform requests. The ordinary challenger separately samples its 32-byte identity seed and 32-byte prekey scalar.

For the adaptive table scans, `symRead_growth` and `symRoot_growth` show that a request can append at most one entry of its own kind. With `h` public table requests and `d` derives remaining, and `c,m` current concrete/message entries, `scanPotential h d c m = 2*h*(m+d) + 2*d*(c+h+m+d)` pays each comparison and every possible continuation. `symRun_decisions` consumes this invariant on the actual adaptive program. `symRun_uniform` similarly charges every source coin and 64 draws for every potential new table entry. Hits, rejected derives and early stopping can only reduce these allowances. These are oracle-query bounds, not a claim about primitive implementation runtime.

## Scope and validation

This closes stage B6, covering steps A1–A3 of the approved hybrid chain. It does not establish the session-collision bound, per-entry KDF replacement, CTX authentication hop, full server-authentication headline, or the separate equality between that experiment and the extracted native formulation. Those stages consume this exact BadB reduction. It changes no protocol source, serialization assumption, primitive implementation, snapshot or persistence scope.

The module contains 138 theorem statements and corresponding guarded dependency reports. Direct Lean 4.34 checks cover the entire module; dependencies are confined to `propext`, `Classical.choice` and `Quot.sound`. Root imports, global checker/inventory wiring and consolidated verification belong to the parent integration stage. No Rust code changed, so mutation testing is not part of this checkpoint.
