# Bound acceptance without an earlier response containing its record

`PqxdhServerAuthRecordPublication.record_publication_with_resources` bounds acceptance without an earlier successful build at the actual source owner whose returned response contains the same decoded record. This strengthens the earlier outer-publication result: the successful build must return the received record's sequence, sender and complete encrypted payload. The theorem uses the literal production-order R1 execution and chronological public request/reply journal. It does not infer source occurrence from equal ciphertext, root or key bytes.

The event is `PqxdhServerAuthPublicationOwnerFamily.observation` instantiated with the new `RecordPublicationEvent.observer` family. It includes acceptance; if no owner is available, acceptance remains in the event and is covered by the existing disclosure/collision partition. For a selected owner, `RecordPublished` requires an earlier successful build, the original first successful finish request, and equal successful decodes of that request and the build's actual returned bytes. The observer receives only the public journal and the fixed coordinate. It does not receive a target secret or a supplied matching session.

## Source join

`PqxdhServerAuthRecordPublicationJoin.written_frame` combines the actual inner and outer writer receipts with the existing abstract `Phase2ReadBack` and `FrameReadBack` contracts. The accepted record matches the retained seal's numeric sequence and sender and its entire encrypted payload. Fixed-width numeric equality identifies the actual writer's frame; readback then supplies the decode of the returned response. Neither writer is assumed total. No canonical encoding, injective encryption, stronger KEM equation or serialization implementation proof is used.

`accepted_published` follows one complete supported source execution. `FinishJournalAcceptance.accepted_receipt` derives the actual successful raw request from the accepted ghost; it is not a caller occurrence premise. `PublicationBuildJournal.accepted_records` associates the retained selected seal with the same earlier successful owner's actual token, pre-build Server state, response and writer calls. Their join gives either the existing ordinary authentication-observer win or the exact decoded-record publication event.

`accepted_clean` divides that same marked execution according to the earlier outer-publication predicate. If an outer response exists, the new source join supplies the stronger record event unless ordinary authentication wins. Otherwise the previous unpublished-attempt argument applies. The conclusion is the same union of ordinary authentication and the private matched-attempt event, so the authentication reduction is charged once in this split.

## Probability and reductions

`PqxdhServerAuthRecordPublicationProbability.full_winning` lifts the source join through the complete joint context and residual samplers. `winning_split` applies a union bound in that same marked probability experiment. `uniform_bound` uses the unchanged ordinary authentication and unpublished-prefix reductions to bound the new decoded-record observer. It does not replace the new observation by the weaker old outer-publication observation.

`record_publication_bound` then composes the new uniform endpoint with the existing original-source owner partition and five schedule changes. Each schedule distinguisher is constructed using the new decoded-record observer. `record_publication_with_resources` pairs this inequality with the proved `ReductionBills` for those exact reductions and the same original source adversary.

Writing `U = entryReductionBudget caps qCoin Q qHash qH` and `H = U + 76`, the bound is:

```text
Pr[accepted without same-record publication at its actual owner]
  <= AdvGapDH(scanClient extractor)
     + choose(Q, 2) * 64 / 2^256
     + sum j in Fin(Q + 1), (recordLoss(j, H) + scheduleLoss(j, newObserver(j))).
```

The `Q + 1` owner sum is explicit; there is no uncharged target-session selection. The unchanged `recordLoss_expanded` theorem expands each record term into three distinct constructed modified nonce-AEAD IND$ advantages, twice the existing modified nonce-AEAD INT-CTXT advantage, `(2H + 1) / 2^128`, and `1 / 2^512`. The three IND$ reductions are ordinary validation, unpublished-prefix validation and the private prefix view. They are not identified with each other merely because they use the same primitive. Each schedule term contains root HMAC expansion, the uniform 32-byte input initial Extract comparison, initial HMAC expansion, the uniform 32-byte input step Extract comparison and step HMAC expansion, with their original concrete samplers.

## Query accounting

The source and reduction budgets are proved conjuncts, not supplied security conclusions. With the fields of `KemCaps` written in words, the exact uniform budget is:

```text
U = 256 + qCoin + 160Q + 64(qHash + qH)
    + keygenUniform + Q * encapsUniform + decapsUniform
    + baseUniform * (keygenBase + Q * encapsBase + decapsBase).
```

The Gap-DH extractor makes zero signing queries, at most `2qH(Q + 1) + 2(Q + 1)(qH + Q + 1) + qH` decision queries, and at most `bodyCoinBudget + 64(qH + Q + 1)` uniform queries. Its complete interpreted game is bounded by `U`. Here `bodyCoinBudget = 128 + qCoin + 96Q + 64qHash + keygenUniform + Q * encapsUniform + decapsUniform + baseUniform * (keygenBase + Q * encapsBase + decapsBase)`. The three HMAC distinguishers have caps 1, 1 and 2; both Extract samplers retain their actual 32-byte uniform draws and the complete base-work ledger in `EntryComponentBills`.

For each selected component, the complete observed client has total, uniform-route and hash-route cap `H`, one selected seal, one raw selected receive, and plaintext bound `Usize.max`. Its interpreted source game has cap `H + 32`. The captured unpublished prefix has the same `H` bounds, one selected seal and zero selected raw receives. The prefix stops before the original raw query; it preserves all preceding source work and its actual optional replies.

Let `B = H + 64(H + 2)` and `B0 = H + 64(H + 1)`. Ordinary validation and integrity reductions have primitive-uniform cap `B`, with seal caps 2 and 1 respectively. Their real experiments have total cap `32 + B`; random validation has cap `B + Usize.max + 32`. Private-prefix validation and view reductions have primitive-uniform cap `B0` and seal caps 2 and 1. Both real experiments have total cap `32 + B0`; random validation has cap `B0 + Usize.max + 32`, and random view has cap `B0 + Usize.max + 16`. These figures include key draws and interpreted primitive/base work. They are oracle bounds, not claims that local parsing, journal scans, arithmetic or allocation have no runtime cost.

## Scope and contracts

The endpoint retains the maintained R1 one-Server/one-Beacon interface, adaptive accept/build/finish requests, public primitive queries, existing allowed installed-key reveals and the source budgets. The target Beacon identity seed is not revealed (`revealSeed = false`). The unchanged approved contracts include the joint twist-inclusive Gap-DH interface, X25519 class and spread laws, actual fixed-HKDF correctness and component games, the restricted 192-byte Extract programmable random oracle, and the shared programmable classical CTX/BLAKE2b random oracle. The latter is stronger than collision resistance. Public HKDF evaluations keep their original semantics; there is no public-HKDF/random-table advantage or old `qRoot / 2^256` interpretation. Primitive implementations and serialization internals remain outside the proof under the explicit abstract message contracts.

Equal decoded record publication is not yet the full eleven-field ProVerif cryptographic-session attribution. In particular, this theorem does not establish equality of attached signature encodings, original signed Phase1 bundle provenance or outer assigned IDs. Those require the ongoing same-occurrence pending-token and joint Ed25519/X25519 consumers. Wider replicated capabilities, later-record composition and the full computational/applied-pi relation remain separate obligations. Snapshots and persistence remain excluded.

The focused package adds eight guarded statements in three modules and ports six unchanged reviewed dependency modules with 47 guarded statements from `972af169dccc1bea4d0cc9bfa16154b1fd2d85e1`. All nine modules receive direct checks. The port retains the corresponding five guides and analysis sections; it does not change their theorem bodies or claim new aggregate verification. Central imports, inventory regeneration and the full verification matrix are integration work.
