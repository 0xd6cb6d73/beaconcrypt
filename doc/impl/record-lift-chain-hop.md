# One hop of the ordered chain hybrid

`PqxdhRecordLiftChainHop` proves one hop of the ordered chain hybrid of `PqxdhRecordLiftChainOrder` over the compiled key-free protocol of `PqxdhRecordLiftIdeal`: for every index `step : Fin (positions * (n * 2))` and every chain decision on the permitted view and the final shared BLAKE2b cache, the hybrids `chains (selected positions step)` and `chains (selected positions (step + 1))` differ by at most the Extract-on-`uniform32` advantage plus the HMAC-PRF advantage of one explicit full 76-byte observer `hopObserver`, each with coefficient one. It is stage C2 of the chain track (item 5, takeover plan §2 S3). The only source contract is `SourceFullCorrect`.

## Statements

`selected_succ` shows that advancing one index makes exactly the selected coordinate `entryAt step` ideal: `selected positions (step + 1) = Function.update (selected positions step) (entryAt step) true`. `finish decision` is the cut observer of a chain decision (it applies the decision to `PqxdhRecordLiftIdeal.viewOf` of the client result and the produced log, and to the final shared cache), and `chains_observe` shows that a chain hybrid followed by a decision is literally the private Protocol run followed by `PqxdhRecordLiftGlobalCut.observe (finish decision)`. `advantage_congr_right` is the congruence of the Boolean advantage under equal laws.

`childUniform_policy` is the positive-depth identification. For a policy that is ideal at a parent coordinate (which satisfies the availability lower bound) and real at its successor, the independent-child endpoint `ProjectionCut.childUniform` of `PqxdhRecordLiftGlobalCut.observed_bound` has the law of the actual Protocol run under the adjacent policy that also idealizes the successor, followed by the same observer. On a completed first-parent prefix (the parent is never looked up) both sides are the same completed run and the extra draws are dropped. On a pending prefix, `PqxdhRecordLiftSourcePrefix.sampled_program` gives the absent successor entry, so `PqxdhRecordLiftChildPolicy.independent_observed` applies for every value of the masked parent half, `GlobalCut.miss_continuation` reassembles the parent draw, `PqxdhRecordLiftPrefixPolicy.sampled_program` shows that the prefix is the same under the adjacent policy, and `FirstLookup.resume_prefix` reassembles the run.

`hop_bound` is the hop. If `entryAt step` is an initial coordinate (depth zero), the hop is the seed cut: `GlobalSeedCut.observed_bound` at the selected slot and direction, with `PqxdhRecordLiftSeedPolicy.uniform_policy` identifying `seedUniform` with the next hybrid. Otherwise the predecessor of `entryAt step` is already ideal (`ChainOrder.selected_predecessor`) and the hop is the parent cut: `GlobalCut.observed_bound` at that predecessor, with `childUniform_policy` identifying the endpoint with the next hybrid. `hopObserver` chooses the corresponding explicit reduction observer: `GlobalSeedCut.reductionObserver` or `GlobalCut.reductionObserver`. Both sample the actual source prefix of the hybrid `selected positions step` themselves (with the retained opposite seed half or the retained 44 bytes of the parent output) and run its complete continuation and the decision.

## Scope

The hop changes the mode of one labelled coordinate and routes every lookup by its label, so no aliasing term arises inside the hop; a run that never reaches the selected coordinate gives equal games inside the cut. The reductions are explicit simulators built from the environment, the adversary, the decision and the index; their query bills are proved in `PqxdhRecordLiftChainBills`. No assumption or contract other than `SourceFullCorrect` is used; Extract-on-`uniform32` and HMAC-PRF enter only as the advantages of these explicit reductions.

## Provenance

New Claude work. It composes the published cuts `PqxdhRecordLiftGlobalCut` and `PqxdhRecordLiftGlobalSeedCut` (Codex) with the published `PqxdhRecordLiftChildPolicy`, `PqxdhRecordLiftPrefixPolicy` and `PqxdhRecordLiftSourcePrefix` and with `PqxdhRecordLiftSeedPolicy`.

## Validation status

All five statements have exact `#print axioms` guards with `propext`, `Classical.choice` and `Quot.sound`. The module passes the focused single-module check against `/tmp/bc-arc-scratch/items45/chain/leanpath` (central `ee7878ee`). The H-7 source scan (version 3) finds no forbidden name. Independent review and central integration are pending.
