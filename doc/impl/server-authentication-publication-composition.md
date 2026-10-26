# Server authentication publication composition

This guide records the numerical and resource consumer of the owner-indexed publication experiment. `PqxdhServerAuthPublication.owner_publication_with_resources` now bounds actual native-order acceptance without an earlier successful outer build at the accepted root owner, together with the complete reduction ledger. The marked-journal inclusion is derived from the same sampled source execution. This is an owner-publication result; the stronger association with the accepted record's complete returned response still needs its separate one-use-token and response-receipt join.

## The same ordinary authentication reductions

`PqxdhServerAuthPublicationComposition.observer_bound` applies to the complete journaled client, including its original context and residual material samplers. The checked `client_authentication` equality says that changing the terminal public observation leaves the entire executable ordinary authentication decision unchanged. The theorem therefore uses the existing `CtxObserverEvent.validation` and `CtxObserverEvent.integrity` reductions with coefficient one. Its right side is precisely the old `ctxLoss`: the constructed validation IND$ advantage, `H/2^128`, twice the constructed modified nonce-AEAD INT-CTXT advantage at index zero, and `2^-512`. It does not reuse the older W1/W2 protocol event, and does not assert that every accepted publication observation is an ordinary forgery.

The hash bound in this statement is an operational certificate for the exact original client. `PublicationResources.source_bills` derives that bound and the remaining counts from the original adversary and KEM caps. There is no honest selected-session premise, writer-totality premise, tag distribution conditioned on failure, or cryptographic security assumption in the observer comparison itself.

## Complete source and reduction costs

`PublicationResources.client_source_budget` proves equality of all generalized resource certificates after interpreting the full component program. Both terminal observations are projections of the same complete sampled run. The equality retains the actual selected-key draw and the full component poststate; it does not infer resource equivalence from a marginal distribution.

`source_bills` specializes that equality and the existing source compiler bounds. Write `U = entryReductionBudget caps qCoin Q qHash qH` and `H = U + 76`. The complete public-observation client has total, uniform and hash caps `H`, selected seal and raw caps one, and total selected plaintext bytes at most `Usize.max`. The interpreted source game pays the additional 32-byte key draw, giving `H + 32`. These are oracle/query bounds, not constant-time or machine-runtime claims about local journal operations.

`reduction_bills` gathers the following exact endpoints into one proved `ReductionBills` value for the same original adversary. Each reduction remains explicitly constructed in the imported component modules.

| Endpoint | Checked counts |
| --- | --- |
| Original joint Gap-DH extractor | Signing zero; decision queries `2*qH*(Q+1) + 2*(Q+1)*(qH+Q+1) + qH`; uniform queries `bodyCoinBudget + 64*(qH+Q+1)`; complete game uniform cap `U`. |
| Owner-observation key schedule | The five newly constructed observation-dependent reductions and their complete `EntryComponentBills`, at `U`, for every `j : Fin (Q+1)`. |
| Ordinary CTX authentication client | Uniform/hash `H`, selected seal/raw one; these are the identical reductions used by `observer_bound`. |
| Ordinary authentication primitive reductions | Put `B = H + 64*(H+2)`. Validation uniform `B`, seals two; integrity uniform `B`, seals one. Each complete real challenger has cap `32+B`. Random validation has cap `B+Usize.max+32`. |
| Actual clean-prefix capture | Total/uniform/hash `H`, selected seal one, selected raw zero, selected plaintext bytes `Usize.max`; all source context/base/KEM work remains included. |
| Unpublished-prefix privacy reductions | Put `B0 = H + 64*(H+1)`. Both ordinary reductions have uniform cap `B0`; validation has two seals and ciphertext-view has one. Each complete real challenger has cap `32+B0`. Random validation has cap `B0+Usize.max+32`, and random view has cap `B0+Usize.max+16`. |

The two privacy reductions are the existing unconditional publication-reference reductions. Their loss is the sum of their two ordinary IND$ advantages, `H/2^128` and `2^-128`. Their raw cap zero is specific to stopping before opening. It does not replace the one-raw authentication allowance. The schedule reductions are the new owner-observation distinguishers, not the older distinguishers for the W1/W2 authentication event. The ledger deliberately projects only the ordinary CTX fields from the old authentication ledger, and supplies all schedule fields from `PublicationOwnerFamily.observed_bills`.

## The completed owner-publication consumer

`PublicationProbability.game` retains the actual uniform selected-key draw, original context and 76-byte residual sampler, complete source state, component caches, ordinary observer history and request-time publication marks. `source_decision` and `ordinary_decision` give exact executable projection equalities for the publication decision and the ordinary authentication decision. No distribution is reconstructed from marginals.

`winning_split` derives the event inclusion on that very run from `PublicationJournalClient.full_winning`: a true publication decision is an ordinary authentication win or an actual matched raw attempt whose stored publication flag was false. It uses the existing abstract `ReadWritable frameWrite frameRead` premise. The outer response writer may still reject. `matched_bound` consumes the marked-history comparison, the exact killed-prefix equality, the journal-erasing capture equality, and the proved clean-prefix privacy bound. Later publication and failed outer writing do not condition the target tag distribution. `ordinary_bound` applies the identical authentication reductions. `uniform_bound` combines the finite probabilities by the ordinary union bound.

`PublicationLoss.recordLoss_expanded` exposes the exact per-owner total. With the names of the constructed reductions made explicit, it is

`Adv_IND$(CtxObserverEvent.validation) + 2*Adv_INT(CtxObserverEvent.integrity) + Adv_IND$(PublicationPrivacy.validation) + Adv_IND$(PublicationPrivacy.view) + (2*H+1)/2^128 + 1/2^512`.

The three IND$ reductions are distinct. Both hash-validation charges remain. The integrity reduction is the original index-zero reduction with coefficient two; the publication comparison adds no target-record guess. `recordLoss_nonneg` records nonnegativity for subsequent finite sums.

`owner_publication_bound` substitutes this bound into the original native-order owner-family experiment. Its left side is actual Beacon acceptance with no successful `.build owner payload` reply before the first successful Beacon finish. If no owner exists, the observation remains counted and is covered by the original disclosure/collision decomposition. The right side is the original constructed joint Gap-DH advantage, `choose(Q,2)*64/2^256`, and the sum over all `Q+1` owner coordinates of `recordLoss` plus the five newly constructed observation-dependent schedule advantages. There is no additional `Q+1` factor beyond this explicit sum. The five advantages are root Expand HMAC PRF, initializer Extract, initializer Expand HMAC PRF, step Extract and step Expand HMAC PRF. They use the proved full-continuation sampler and the actual shared output projections.

`owner_publication_with_resources` conjoins that inequality and `PublicationResources.ReductionBills`, so the precise same constructed reductions carry the ledger above. The full source budget is

`U = 256 + qCoin + 160*Q + 64*(qHash+qH) + keygenUniform + Q*encapsUniform + decapsUniform + baseUniform*(keygenBase + Q*encapsBase + decapsBase)`.

The schedule reductions have HMAC challenge caps 1, 1 and 2. Their real/random challenger uniform caps are respectively `64+U / 64+U`, `32+U / 96+U`, `64+U / 64+U`, `64+U / 128+U`, and `96+U / 160+U`. Both Extract input samplers draw exactly 32 bytes. Public fixed HKDF computations remain real outside the approved restricted Extract-ROM interface. No public-HKDF/random-table interpretation or independent-projection assumption appears.

## Scope and remaining correspondence

The theorem remains in the approved R1 experiment: one fresh Beacon pinned to one fresh Server identity, arbitrary adaptive accept/build and raw initial-response delivery, real optional replies and rejections, public HMAC/hash queries, and installed-chain reveals. There is no Beacon secret reveal or Server-seed reveal in this bound, and no KCI claim. The permanent contracts are the approved restricted programmable zero-salt Extract oracle on 192-byte inputs, the shared CTX/BLAKE2b programmable classical random oracle (stronger than collision resistance), the joint twist-inclusive Gap-DH interface, X25519 class and spread laws, source full Extract/Expand wiring, ordinary constructed component games, and the abstract message-model read/write premise. No new primitive or protocol-authentication premise is introduced.

Successful publication at the right owner is now proved. Equality with the accepted record's complete returned response, and its full symbolic eleven-field event projection, are not conclusions of this theorem. They require the one-use pending-token and exact builder-receipt consumer. Global replicated sessions, later-record composition and the source-to-symbolic capability map remain separate full-proof obligations. No assigned-ID agreement, serialization implementation, persistence, restoration or primitive-internal theorem is claimed.

The two numerical modules and headline add ten public statements with exact standard-axiom guards. The prior four observer/ledger statements are unchanged. The supporting 16-statement `PublicationJournalClean` and 11-statement `PublicationJournalClient` modules and their guides are exact reviewed ports from `ca018e91` and `25f41fd8`; their full explanations are retained in the analysis. This checkpoint changes only Lean and documentation. Root import, trust-boundary inventory and aggregate verification remain central integration work after the complete publication-origin consumer is reviewed.
