# R1 authentication in the raw registration scheduler

This lane connects the existing complete R1 session and decoded-record authentication bound to the actual singleton program of the raw registration scheduler. It includes Server construction, Beacon construction, the first optional bundle publication, both initialization calls, every original adaptive suffix request and every refused branch. It does not generalize that bound to arbitrary multi-owner schedules or claim completion of the global computational/symbolic bridge.

The production basis is the Rust source shared with the central `codex/full-proof-composition` branch, including the Beacon sequence-one check. `Beacon::try_new` at `beaconcrypt/src/beacon.rs:65-82` calls initialization, checks the pin's 32-byte width, then draws the identity, prekey and KEM pair. It does not validate the pin as a curve point. `Server::try_new` at `beaconcrypt/src/server.rs:154` performs initialization and then supplied-seed parsing or seed generation. `finish_registration` at `beaconcrypt/src/beacon.rs:403` retains the actual phase restriction and conversion, KEM, DH, root and record processing. Serialization implementations and native primitive algorithms remain outside this proof under the existing functional contracts.

## Exact scope

There is one constructed Server and one attempted Beacon owner, allocated at public index zero when creation succeeds. The caller sees one raw create reply, one first-bundle reply and then the original seven capabilities: uniform coins, arbitrary-byte Server accept, pending-token build, arbitrary-byte Beacon finish routed to owner zero, public HMAC, shared hash and current-kernel reveal. The suffix remains fully adaptive in all actual optional replies; rejected requests, retries, missing tokens and attempts after acceptance remain in the run. The source equations also allow the suffix to read the actual create reply. The security endpoint uses the original R1 suffix whose input is the public identity, Server key ID, optional Phase 1 and no Server seed; the create reply is ignored by that original interface.

Operational equations cover both generated and supplied Server seeds. The computational bound covers only the generated-Server branch. Every actual constructor refusal yields a false target event, and the rejected Beacon construction branch still executes the missing-owner bundle and suffix. The proof never assumes that a random seed is uniform after conditioning on constructor success.

The failure event is exactly `PqxdhServerAuthCommonEvent.Failure`: the Beacon accepted, but no Server-session index has both the existing eleven-field `Common` agreement and publication of the exact accepted decoded record in the same chronological call journal. It does not assume an honest submitted candidate, matching partner, successful writer or unchanged signed fields. The existing R1 theorem's reveal behavior and freshness discipline are unchanged. This is not assigned-ID agreement for later records, a KCI statement, or a theorem about arbitrary replicated sessions.

## How the connection is checked

The original five lane modules already prove 49 public operational statements. `PqxdhRegistrationR1Restriction` materializes the private prekey and KEM handles and relates all seven callbacks, full adaptive continuations and both primitive caches. `PqxdhRegistrationR1Audit` erases only ghost and family histories from the operational scheduler while retaining the original complete R1 audit on the other side. `PqxdhRegistrationR1Initial` proves the actual seed → prekey → KEM → one-time draw order and all three signatures before the optional writer. `PqxdhRegistrationR1Surface` includes both initialization gates and the width-only pin parse. `PqxdhRegistrationR1Journal` records the actual create reply, actual bundle reply and every routed suffix query/reply. Their detailed statement inventory and previous validation remain in `handover/pause-2026-10-01/r1-restriction/README.md`.

The new cohort adds 28 guarded statements in six modules. Existing theorem statements are unchanged. The 109 absent dependencies were copied byte for byte from published `adabe9af29a9793400e1465e62989770482bde9d`; the exact source and reused artifact hashes are recorded in `handover/pause-2026-10-01/r1-restriction/evidence/common-authentication-port.json`. Their source bytes also match the completed `edc701e` integration build. This port adds no new primitive assumption or reduction claim.

| Module | Statements | What is proved |
| --- | --- | --- |
| `PqxdhRegistrationR1RootAudit` | `native_root`, `native_public`, `context_input`, `audited_root`, `journal_public`, `generated_order` | One source-ordered execution supplies the entire original native audit and the common authentication outcome. The actual Phase 1 result establishes the source invariant, public input matches literally, and the generated order is an exact program equality with the existing ordered game. |
| `PqxdhRegistrationR1RootJournal` | `program_journal`, `execution_journal`, `recorded_root`, `execution_map`, `recorded_surface` | The public journal, complete private occurrence receipts, local samples, shared caches and return value are kept jointly. The actual two prefix replies followed by the public projection of the private call log equal the real surface journal. No second independent run supplies the event witness. |
| `PqxdhRegistrationR1RootSurface` | `prefix_audit`, `experiment_audit`, `surface_audit`, `surface_journal` | Both initialization calls, every constructor outcome, the final runtime and the full raw singleton execution factor through that same private root audit. Supplied seeds remain operationally exact. |
| `PqxdhRegistrationR1RootProbability` | `prefix_probability`, `generated_probability`, `generated_failure_le` | Dropping the second and then the first initialization gate can only increase the target probability. The proof sums the actual runtime outcomes and retains the refused tail on the source side. There is no new selection loss or successful-constructor premise. |
| `PqxdhRegistrationR1Authentication` | `unit_queries`, `budget_iff`, `generated_authentication` | Erasing only the caller's return value preserves all selective query caps. The existing complete common-authentication bound and its exact `ReductionBills` apply to the generated source experiment through the proved gate inequality. |
| `PqxdhRegistrationR1Resources` | `route_bound`, `program_bills`, `source_uniform`, `generated_uniform_bill`, `accept_class`, `build_class`, `source_ledger` | One routed suffix request remains one request of its original class; the actual prefix adds one create and one bundle. The separate source bill includes both initialization callbacks and the complete interpreted KEM work. Consumed registrations remain unique; all accept/build attempts bound sessions and Server-counter growth. |

The journal statements deliberately retain more than equality of marginal states. `RootAudit` contains the full `RootExecution.Outcome`, including context, generation coordinate, private source and root receipts and primitive-family state, together with the caller's result. `recorded_surface` adds the public surface journal while retaining that entire outcome. The public caller never receives the private annotation.

## Bound and query accounting

Write `A` for the original caller with only its final return value mapped to unit. The resulting failure bound is exactly the existing common-authentication bound:

```text
Pr[source accepted without common session and published record]
  <= AdvGapDH[extractor(scanClient A)]
     + choose(Q, 2) * 64 / 2^256
     + sum j in Fin(Q + 1) (recordLoss(A, j, H) + scheduleLoss(A, j))
     + AdvJointEUF[reduction(A)]
H = entryReductionBudget(caps, qCoin, Q, qHash, qH) + 76
```

The reduction functions, record and schedule observers, selection sum and constants are the literal definitions in `PqxdhServerAuthCommonAuthentication.common_authentication_with_resources`. They are not replaced by a list of primitive names. In particular the Ed25519/X25519 joint-use reduction is charged once, and the same existing record/CTX and five schedule reductions remain. The new gate transport has coefficient one and adds no collision or guessing term. The complete `ReductionBills` proposition is returned alongside the inequality: it includes every record reduction bill, the signing cap 3, the converted-DH cap `qFinish`, the full local uniform cost `reductionCost(caps, qTotal)` and the joint game's `32 + reductionCost(caps, qTotal)` bound. The source caps count attempted calls, including rejected finish attempts.

Source work is accounted separately because the constructed cryptographic reductions use the gate-free ordered experiment. Let `I` bound each actual initialization callback; let `G = keygenUniform + baseUniform * keygenBase`, `E = encapsUniform + baseUniform * encapsBase` and `D = decapsUniform + baseUniform * decapsBase`. Let the suffix caps be `qCoin`, `qAccept`, `qBuild`, `qFinish`, `qHmac`, `qHash` and `qReveal`. Coordinates 1 and 2 of the nine-class vector are zero for that suffix. The generated source experiment has the checked conservative uniform-query bill:

```text
2*I + 128 + G + qCoin
  + (96 + E)*qAccept + 64*qBuild
  + (69*max(64, D))*qFinish + 64*qHmac + 64*qHash
```

The 128 bytes are the Server seed, Beacon identity seed, prekey scalar and one-time scalar. KEM generation is the separate complete `G` bill. The first bundle retains three deterministic signing-service requests and one optional writer, under the already checked `JointCreation.client_bills` and `JointBundle.client_bills` interfaces. Every public finish retains the existing 69-callback conservative bill, including work performed before sequence or binding rejection. The reveal service has no uniform-oracle request in this interface; that is not a claim of zero CPU or storage work. Deterministic parsing, signature verification, conversion, DH, real public HMAC/Expand and writing remain actual local computations or existing primitive contracts. Unknown KEM base work is never counted as free.

`source_ledger` additionally proves, for every supported complete source run, that consumed registrations are duplicate-free, their count and allocated sessions are at most `qAccept`, and the Server allocation counter stays between its initial value and that value plus `qBuild`. These are bounds on all attempts and do not infer agreement between claimed and assigned IDs.

## Contracts and remaining integration

No existing theorem is weakened or deleted. The endpoint retains the exact prior functional/source correctness, X25519 class/spread, attached-verification adapter, codec read-back/writability and fallback hypotheses. The restricted programmable Extract ROM at the actual root input and the shared programmable classical CTX/BLAKE2b ROM remain explicit existing boundaries. The cryptographic implementations are correct black boxes. Public HMAC and Expand outside those stated patches remain real; there is no public-HKDF/random-table interpretation or new protocol-shaped security assumption.

Snapshot and persistence behavior, serialization implementations, compiler correctness, allocator/OS behavior and physical erasure are outside this lane. The code does not introduce a persistence premise or restoration analysis. Supplied Server seeds receive no generated-key security guarantee. Arbitrary dynamic multi-owner schedules, replicated session selection, the global reveal/freshness composition and the complete ProVerif event mapping remain separate global work.

This topic-lane checkpoint passed two independent semantic reviews on 2026-10-05 and awaits central integration. Both reviews approved the theorem scope, assumptions, source correspondence and accounting; one historical-status prose nit was corrected without changing Lean source. The frozen reviewed manifest and the review receipts are retained in `handover/pause-2026-10-01/r1-restriction/evidence/`. Six changed modules are checked directly under Lean 4.34 with one process, a shared lock and exact standard-axiom guards; no full aggregate build, Rust or ProVerif rerun is claimed for this cohort. All new guards allow only `propext`, `Classical.choice` and `Quot.sound`. Integration must use a fresh topic from current central, semantically port the new lane modules and its prior reviewed dependencies, and regenerate the shared root imports, checker and inventory metadata; the 109 unchanged authentication dependencies already exist in central and must not be ported twice.
