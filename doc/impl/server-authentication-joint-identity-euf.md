# Source authentication with the joint identity challenger

This checkpoint proves an all-attempt, coefficient-one weak-EUF reduction for changed signed Phase1 fields in the actual R1 native experiment. It uses the previously approved joint Ed25519/converted-X25519 endpoint. That endpoint exposes ordinary detached signing and optional static DH from the same sampled identity seed, and its winning event is valid verification on a message absent from the signing log. It does not assume protocol authentication. Ordinary Ed25519 EUF-CMA without the auxiliary DH interface is not claimed to suffice.

## Source experiment and event

`PqxdhServerAuthJointIdentityEuf.sourceBad` generates the Server seed, Beacon seed, Beacon prekey, actual KEM keypair, and one-time scalar in production constructor order. It runs the literal Phase1 publication and the original complete `nativeHandler` API with the original state, caches, optional replies, and chronological public journal. Its terminal event re-reads every original raw accept request using the original abstract reader and four field getters. It then tests whether any candidate passes the ordinary detached verification/parsing interface under the target Beacon identity but differs in at least one unsigned prekey, one-time key, or KEM public key. The original run includes unchanged honest candidates, changed candidates, attacker-owned identities, malformed inputs, rejection, writer refusal, arbitrary scheduling, and installed-kernel reveals. A rejected source call with publicly valid changed fields may also satisfy this terminal event; this deliberately enlarges the event available to a source-authentication consumer.

The run has one generated target Beacon identity and one locally generated Server identity. The target identity seed is not a public API capability. This theorem does not close replicated-session selection, the full eleven-field registration-origin event, or the global computational/symbolic experiment.

## Exact history and concrete extraction

`PqxdhServerAuthJointIdentityLog.sign_run` and `phase1_history` establish the actual request and returned-signature log: prekey, one-time key, then KEM public key. The latter preserves the entire retained Phase1 output and private state, including failed serialization. The `simulate_quiet`, `coins_quiet`, `auxiliary_quiet`, `prefix_quiet`, `prepare_quiet`, `stage_quiet`, `finish_quiet`, `handler_quiet`, and `program_quiet` statements show that no subsequent native operation can add a signing request. Optional converted-identity DH and all local KEM/base/randomness computations remain in their original continuation. `quiet_history` preserves the signed-message subsequence without discarding intervening recorded DH events. `execution_history` combines these facts for the complete execution; `coins_history` preserves the whole signature/DH history while local sampling executes. Uniform draws remain computations on the uniform interface; they are not claimed to be events in the joint signature/DH history.

`capture` is a concrete primitive adversary prefix. It receives only the joint public keys, locally samples the other source material, and calls the previously checked seed-free compiler. The unavailable target seed remains in the challenger. Only locally known unsigned material and the original public journal are returned for extraction; the complete private native state is nevertheless executed before this final projection. `capture_history` proves that these exact locally generated fields supply the entire actual signing log.

`extract` scans the original attached candidate fields in the Server's PQ/prekey/one-time verification order and selects the first detached signature that verifies under the target key on a message outside the actual three-message log. It uses no secret, recovered plaintext, guessing oracle, field selection, or attempt selection. The generic existing structural results for accepted Phase1 fields imply `extract_wins`. `reduction_game` checks that the ordinary joint weak-EUF game uses exactly this capture and exact final history. `routed_bound` gives the coefficient-one event inclusion in that common experiment.

`capture_plain` and `capture_observation` identify the complete original native execution before the final event projection. `source_routed` applies the already proved seed-order law to the entire evaluated continuation, including private state and public replies; it does not exchange only marginal key distributions. `source_bound` concludes:

```text
Pr[any publicly valid, same-target changed Phase1 field in the original native run]
  <= Adv_joint-Ed25519/converted-X25519-weak-EUF(the concrete reduction).
```

There is no factor for three signed fields, the number of accept calls, or a guessed candidate identity. The same-target condition belongs to the bad event; the game does not require the attacker to supply an honest candidate.

## Joining actual acceptance

`rawCandidate_receipt`, `candidates_member`, and `changed_member` connect an actual journaled raw accept and its original decoder/getter receipt to the scanned event. The separate source-receipt lane proves that an actual successful accept supplies those receipts and the exact unsigned tuple. Translating the source's arbitrary attached-verification buffers to detached verification retains the existing explicit `HasAttachedVerificationAdapter` contract. The one-way `SourceWiring.verifyAttached` law on already well-formed buffers must not be silently substituted for that full adapter. No serialization implementation, canonical encoding, constructor injectivity, or signature uniqueness is assumed here.

## Query accounting and remaining work

`PqxdhServerAuthJointIdentityResources.phase1_signing`, `execution_signing`, `capture_signing`, and `reduction_signing` prove signing cap 3 for the actual constructed reduction under every reply branch. `reduction_queries` proves that final extraction preserves every predicate-based cap of the complete capture, including uniform and optional static-DH queries. `fields_length` and `journal_fields_length` bound the local detached-verification scan by three fields per original public API call; the earlier source verification work still runs. These list bounds do not assert a machine-runtime bound for arbitrary raw input lengths or codec functions.

No local sampler, KEM generation, encapsulation, decapsulation, base interpreter, or public HMAC/CTX computation is declared free. Their programs are retained literally. Expanding this reduction's remaining uniform, base and static-DH caps into the global protocol ledger is still an integration obligation; the source-bound inequality is not presented as closing that ledger. The full eleven-field event must also combine this single EUF charge with the previously constructed root, record, publication and schedule bounds in the same native experiment. Those consumers, the later-record closure, and the common symbolic capability experiment remain active work.

## Validation scope

The checkpoint has three Lean modules and 32 public theorem statements. Focused module checks and a guarded axiom print for each statement are required before publication, with only `propext`, `Classical.choice`, and `Quot.sound` permitted. Independent reviews cover the statements, actual source continuation, endpoint interface, target-seed confinement, query claims and residual obligations. This is a proof-only topic checkpoint; root imports, trust inventory and the complete Make verification matrix are reconciled on the combined integration result. No Rust or primitive implementation is changed.
