# Exact ProVerif verdict classification and HKDF prefix fidelity

The P6 inventory classifies each maintained expected verdict without changing its formula, polarity, symbolic process or primitive theory. It separates security queries from functional fixtures, definitions, witnesses, controls and unresolved diagnostics. This stage adds no ProVerif security proof, computational reduction, primitive assumption or source/model simulation.

The original P6 basis is `787319ade78ee9e0b599dc349fdc8b5cf6cbf7c0`. The [joined integration](proverif-verdict-integration.md), based on `9be4f3ea1cb9b8a3f753b5cd96bc63b7a665c700`, adds the published moved-pending scheduler and open CTX differential pair. The subsequent [P5 integration](proverif-strong-secrecy-integration.md), based on `3ead9cb5ed44f9c54f038ac647fd063a2c2172cc`, adds its two bounded active equivalences and four fresh-secret controls. The later [A2 projection](proverif-registration-provenance.md) adds three scoped T0 provenance/identity-secrecy expectations and three witness/control expectations. The completeness checker rejects an unrecognized new `check-*.py` entry point, so those additions cannot silently escape classification.

## Manifest and mechanically checked completeness

`beaconcrypt-core/proofs/pro-verif/verdict-classes.tsv` has one row per expected primary or explicitly checked secondary verdict. Its key is the checker, target and position within that checker's expectation list. The row records the exact formula SHA-256, expected status, one class and the scope. Repeated primary/final-summary copies of the same verdict are one entry. Checked `(even ...)` and `(but ...)` secondary statements have separate entries. Run `python3 beaconcrypt-core/proofs/pro-verif/check-verdict-classes.py --show` to print every complete formula alongside its classification. This also lists the eight complete unresolved formulas below.

`verdict-inventory.py` derives the roster from the maintained gates. For AWK, it observes the existing expectation calculations in memory and feeds the resulting synthetic transcript back to the unchanged checker. The synthetic transcript tests metadata acceptance; it is never recorded as a ProVerif success. For the three local registration Python drivers, isolated imported modules execute only their existing fixture-generation and expectation-selection code in temporary directories: the ProVerif `run` boundary returns a target label, and the checking boundary records the formula/status arguments. No prover subprocess is invoked. The general-registration checker now calls its unchanged expected-results calculation through a pure helper used by both the gate and the inventory. Its complete expectation block was compared structurally with the prior block; only the final assignment became a return. The fs, primitive-profile, moved-pending, open-CTX, active strong-secrecy, signature-provenance, KEM-controller and alias expectations are read from their maintained rosters and source-selected queries. Every recognized checker must have entries, and every expectation must have exactly one row; missing, substituted, duplicate or extra rows fail.

The source test `proverif_verdict_classes_cover_every_checker_and_profile` invokes this inexpensive metadata gate from the transcript-fidelity suite. The Make transcript-fidelity target also runs the independent checker regressions. Those regressions reject missing fail-stop, chosen-message, pin-free and pin-read targets; unknown results relabelled as evidence; formula/status substitution; fixture promotion; changed fs bounds/hooks; and omitted secondary verdicts. The full fs scope string contains the exact bound, query file and ordered library list, so profiles cannot be conflated merely because they have the same query formula. Pending-token scopes additionally name the concrete fixture and its object/accept/build limits; open-CTX scopes name the replicated process and public weak-AEAD context/frame interface. Two new regressions reject omission, promotion or scope replacement of any of those six rows. A deliberately reusable token has its own negative-control row even though its query file is shared with the normal one-use fixture. The six P5 rows additionally pin the exact main process, directional bounds, challenge eligibility or its deliberate removal, ordinary public result-bit interface, query file and ordered libraries. Two further regressions reject missing P5 controls, altered bounds/process selectors, a falsely advertised optional-plaintext oracle or changed classes. The two equivalence TRUE expectations remain separate from the controls' fresh-secret FALSE expectations.

## Classes and counts

The six D7 classes are retained: `security`, `witness`, `negative-control`, `differential-control`, `definitional`, and `limitation`. Functional fixtures are the `definitional` class with an explicit fixture scope. The manifest adds one necessary category: `diagnostic` is reserved for an existing `unknown`/`cannot be proved` expectation. Unknowns count as neither a proof nor a counterexample. A TRUE inverted control or residual weaker statement in a control run is labelled `differential-control`; it is not described as a reconstructed attack. The original checkers retain their exact trace requirements.

The current manifest contains 3,165 expected statements: 170 security-class entries, 2,836 definitional/fixture entries, 84 witnesses, 28 negative-control entries, 19 differential-control entries, 20 limitations and eight diagnostics. The original 3,147 rows and their classifications remain unchanged. These are counts of classified expectations, not new validation receipts or counts of independent protocol theorems. In particular, the general-registration family includes many conditional statements with unreachable antecedents; repeated targets and projections must not be added together as independent security guarantees. Only `security` rows may be counted when reporting security-query results, and their actual receipts, theory and scope must accompany that report.

| Checker | Security-class expectations | Other expectations | Exact scope |
| --- | ---: | ---: | --- |
| Legacy AWK | 58 | 208 | Original fixed schedules, passive equivalences, component services and controls |
| General registration | 61 | 2,383 | All 2,444 retained generated cases; sequence-one admission; explicit projections |
| Free schedule | 20 | 32 | Every current registration, s2b, b2s, fail-stop, chosen-message and pin profile |
| Primitive fidelity | 4 | 5 | Bounded role-asymmetric encoding profile, unchanged theory contract |
| KEM controller | 9 | 22 | Original authentication, witnesses and exposed-identity controls, including four secondary statements |
| X25519 alias | 12 | 4 | Canonical and projected one-session correspondences; exact-byte origin limitation |
| Local Server admission | 1 | 15 | Honest-identity signature origin plus local instrumentation/control diagnostics |
| Local response boundary | 0 | 74 | Field/counter/order relations, finite tails and six unresolved diagnostics |
| Local Beacon boundary | 0 | 239 | Local order/field relations, finite retry tails and one unresolved diagnostic |
| Moved pending tokens | 0 | 4 | Finite cross-object/reverse-build witnesses, one-use fixture and explicit reuse control |
| Open CTX pair | 0 | 2 | Definitional context binding and weak-AEAD differential control with arbitrary public contexts/frame |
| Active strong secrecy | 2 | 4 | Exact bounded directional equivalence; labelled result bits; separate single-world fresh-secret controls |
| Signature provenance | 3 | 3 | Exact T0 single-publication and role-DH projection, source-profile A2 lift, auxiliary identity secrecy and purpose/triple controls |

## Correct interpretation of the fixtures

The two `hkdf-prefix-conformance` expectations are FALSE reachability statements: equality events execute because the letfun expressions are identical. They are definitional checks, not a security result or an HKDF proof. The new `hkdf_prefix_smoke_has_an_exact_source_projection_check` compares compact symbolic definitions of both initial directions, `ratchet_next` and `ratchet_material` with the complete native `ratchet_step_from_response` body. The body must use the one split response's next-chain, key and nonce fields exactly. The existing compiled-core test separately checks the 64/76-byte arrays: first32 is the Server send chain and step key, second32 is the Server receive chain and next chain, final12 is the nonce, and Beacon directions are reversed. Existing initial-ratchet fidelity checks retain actual HKDF-SHA-512/no-salt invocation, shared symmetric label and 64/76 widths. Correct HKDF implementation and prefix consistency remain primitive contracts; these tests verify protocol wiring and projections rather than primitive internals.

The closed AEAD context, public-key purpose/algorithm, Phase2 binding and HKDF endpoint fixtures are not promoted to protocol authentication or primitive commitment results. Their FALSE differential sides show that changing the symbolic definitions changes the fixture outcome. Strong constructor properties remain explicit idealizations. The legacy scenarios, exact queries and controls are retained; this classification does not delete or replace them.

The two `failed-receive-compromise` correspondences whose conclusion passes `entry_state` twice into `ReceiveStateCompromised` are definitional fixtures. Their TRUE verdict cannot establish native rollback neutrality. The other finite receive state/order correspondences retain their fixed-fixture scope. Actual failure neutrality comes from the Lean `RatchetReceiveRollback.receiveNext_failure_entry`/raw receive results and the source failure path, while adversarial scheduling is addressed separately by the fs C1/C3/C5/C-STALE results. This creates no snapshot, persistence or restoration claim.

The response boundary's `Return(before,before)` and the Beacon boundary's explicitly constructed state/order events are also local facts or fixtures. Native counter and lifecycle facts come from `PqxdhRegistrationResponse.build_counter` and `PqxdhRegistrationBeacon.no_rebuild`/`no_retry`, with their stated interfaces. The manifest does not reinterpret local instrumentation as whole-protocol authentication. The response tail and Beacon retry controls remain useful functional regressions, including their success/failure and mutation traces.

The original baseline and active-classical 14-query gates remain intact and are labelled fixed-schedule regression results. The later/post-registration and main candidate controls retain their exact gates and are labelled finite functional fixtures. No general later assigned-ID agreement is claimed.

## The complete generated registration family

All 2,444 expected results, all 53 targets 0..52 and all generated cached positions are retained. Production and the current model admit an initial completion only at sequence 1; target 0 and targets 2..52 cannot complete. The older statement that every initial target 1..51 is accepted predates the owner's sequence-one change and must not be reused. Established receive capacity remains a separate source interface.

Queries 1 and 2 are session/accepted-record origin; query 3 is target-one reachability or other-target rejection; queries 4..8 test binding/framing/initial-sequence conditions; query 9 identifies the committed source-order poststate; queries 10..16 cover the explicit continuation's record origin, availability and replay events. Their manifest scopes state when the initial-completion antecedent is unreachable. Query 17 is the explicit continuation/poststate connection. Queries 18..22 are the source-tag specialization guards. Query 23 at targets 1..51 is the material-parametric cache-pop destructor component, not a protocol authentication query. At targets 0 and 52 its unchanged absence statement remains classified with that generated case's rejection scope. The classifier does not replace a result by an implication from another result or drop a cached position. The runner's regex-checked causal, sender-prefix and fixed-target rewrites remain disclosed assumptions of this finite decomposition, with the existing source/Lean obligations.

### Per-query classification and implication table

The source process emits `GeneralAdmissionCompleted` before `GeneralAdmissionPoststate` and before the only output on the private `general_admitted_states` channel. `GeneralAdmissionRelabelled` is also after completion. `GeneralAdmissionContinue` can emit its entry event only after consuming that private handoff; all future/cached/initial-target events are below that entry, and replay events are below cached acceptance. These are syntactic event-order observations about the maintained model, not a Rust-to-ProVerif simulation theorem. They explain the conservative classification below while leaving every original checker execution and projection obligation in place.

| Query indices | Target 0 or 2..52 | Target 1 |
| --- | --- | --- |
| 1, 2 | Definitional: query 3 proves absence of the common completion antecedent | Security: session and exact accepted-record origin |
| 3 | Security: direct initial-completion rejection by the production sequence-one policy (0/52 also exceed the defined initial plan) | Witness: actual completion is reachable |
| 4, 5, 6, 8 | Definitional: restricted completion events or implications follow from query 3's absence | Security: malformed/short/empty/binding admission conditions |
| 7 | Definitional: relabel event is a descendant of excluded completion | Security: initial claimed-ID relabel rejection, not later assigned-ID equality |
| 9 | Definitional: poststate event occurs only after excluded completion | Security: full reached poststate agrees with the source-order origin |
| 10, 12 | Definitional: cached acceptance requires the excluded private handoff | Definitional: `general_prefix_1` installs `receive_cache_empty`; no cached acceptance is reachable |
| 11 | Definitional: future acceptance requires the excluded private handoff | Security: exact origin of an immediate future record |
| 13 | Definitional: future acceptance requires the excluded private handoff | Witness: immediate future acceptance is reachable |
| 14, 15 | Definitional: either replay event is below excluded cached acceptance | Definitional: either replay event is below the empty-cache acceptance branch |
| 16 | Definitional: retained-target event requires the excluded private handoff | Definitional: the empty cache returns `general_cache_missing` for the consumed initial target |
| 17 | Definitional: explicit handoff origin with an excluded continuation antecedent | Definitional: explicit private handoff instrumentation |
| 18, 19 | Definitional: excluded completion/poststate antecedents | Definitional: source sequence-specialization guards |
| 20 | Definitional: excluded future-acceptance antecedent | Definitional: next-sequence specialization guard |
| 21 | Definitional: excluded retained-target antecedent | Definitional: empty-cache retained-target antecedent |
| 22 | Definitional: excluded continuation antecedent | Definitional: source sequence-specialization guard |
| 23 | Targets 2..51: independent definitional cache-range component for all 1..target-1 positions; targets 0/52: excluded cached-acceptance antecedent | Definitional: independent empty-cache destructor component |

This table preserves all 2,444 per-target/per-position statements. It removes no result as redundant and replaces no solver run by a claimed implication. The classification gate prevents promotion of the listed unreachable-antecedent or empty-cache entries into security counts. Their continued successful validation remains useful for detecting source/projection drift.

## Unresolved exact diagnostics

The following entries remain required by their existing gates. They are not attacks, proofs, or evidence that the native property is false. The five mutated response formulas are sensitivity diagnostics; their unknowns do not establish counterexamples. The three unmutated diagnostics concern replicated mutex/token reasoning or full-process publication reachability. The source Lean facts do not turn an unknown ProVerif verdict into TRUE.

- `check-registration-set.py` / `mutex-inconclusive-diagnostic` / 1: `event(RegistrationSetConsumed(owner_2,first,rid_1)) && event(RegistrationSetConsumed(owner_2,second,rid_1)) ==> first = second` — UNKNOWN.

- `check-registration-response.py` / `counter-jump` / 2: `event(RegistrationResponsePublished(owner_3,token_1,before_1,next_1,assigned_2,plaintext_1,frame_1,response_1)) ==> next_1 = before_1 + 1` — UNKNOWN.

- `check-registration-response.py` / `counter-jump` / 6: `event(RegistrationResponseCompleted(owner_3,token_1,before_1,after,true)) ==> after = before_1 + 1` — UNKNOWN.

- `check-registration-response.py` / `wrong-chain` / 7: `event(RegistrationResponseInstalled(owner_3,token_1,assigned_2,ad,send,receive)) ==> event(RegistrationResponsePrepared(owner_3,token_1,next_1,root_3,hkdf_first_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain)),hkdf_second_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain)))) && assigned_2 = registration_response_identifier(next_1) && send = hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain)),symmetric_ratchet_domain)) && receive = hkdf_second_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain))` — UNKNOWN.

- `check-registration-response.py` / `wrong-binding` / 8: `event(RegistrationResponsePublished(owner_3,token_1,before_1,next_1,assigned_2,plaintext_1,frame_1,response_1)) ==> plaintext_1 = registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(assigned_2)),registration_response_nonempty(suffix))` — UNKNOWN.

- `check-registration-response.py` / `failure-counter` / 5: `event(RegistrationResponseCompleted(owner_3,token_1,before_1,after_13,false)) ==> after_13 = before_1` — UNKNOWN.

- `check-registration-response.py` / `reachability-inconclusive` / 1: `not event(RegistrationResponsePublished(owner_3,token_1,before_1,next_1,assigned_2,plaintext_1,frame_1,response_1))` — UNKNOWN.

- `check-registration-beacon.py` / `correspondences` / 7: `event(RegistrationBeaconClosedRejected(owner_2,attempt_2)) ==> event(RegistrationBeaconAttempt(owner_2,prior,raw_1))` — UNKNOWN.

No primitive implementation, Rust protocol code, wire format, symbolic process, secrecy/authentication formula, reveal rule or computational budget changed in this stage. Existing ProVerif results are reused only because their inputs and expectation formulas are unchanged. New verification is limited to checker regressions, transcript/source fidelity, formatting and the reviewed inventory. The global composition and source-schedule obligations remain open.

The signature-provenance rows pin their one- or two-publication bound, exact purpose parser/control, replicated owner/DH/observer interface, process selector, query and ordered libraries. Its three security-class expectations include two auxiliary ideal identity-secrecy statements; they are not three independent end-to-end protocol theorems. A regression rejects omissions, class promotions and falsely unscoped full-protocol descriptions for every new row.
