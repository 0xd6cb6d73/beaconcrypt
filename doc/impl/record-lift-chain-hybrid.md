# The complete ordered chain hybrid

`PqxdhRecordLiftChainHybrid` telescopes the hops of `PqxdhRecordLiftChainHop` over all `hops n budget = positions budget * (n * 2)` indices of `PqxdhRecordLiftChainOrder`, where `positions budget = sends + 51 * receives` is the frozen derivation allowance `Caps.derivations`. It is stage C3 of the chain track (item 5, takeover plan §2 S3). The only source contract is `SourceFullCorrect`.

## Endpoints

Index zero is `realChains` (`PqxdhRecordLiftIdeal.chains_selected_zero`), the frozen record world on the CE-12 analysis projection (`realChains_analysis`). The last index `selected (positions budget) (hops n budget)` is ideal exactly on the coordinates of depth below `positions budget` (`ChainOrder.selected_last`). `terminal_safe` shows that, for every adversary within its budget, every lookup reached by that hybrid's run is at such a coordinate: the coordinate is populated in every supported final table (`PqxdhRecordLiftSeedPolicy.lookup_present`, `present_preserved`, `reaches_final`), and every populated coordinate of a final table has depth below the executed native KDF count, which is at most `sends + 51 * receives` (`PqxdhRecordLiftMixedWorld.protocol_run_bounds`, from `run_kdf` and `run_depth`). `chains_terminal` turns this support-level congruence into the equality of the terminal hybrid with `idealChains` (`PqxdhRecordLiftSeedPolicy.run_agrees`), for every environment and every adversary with `budget.Respects`.

## Bound

`telescope` bounds the advantage between the first and last of a finite sequence of Boolean games by the sum of adjacent advantages (triangle inequality). `extractAdvantage` and `prfAdvantage` are the two real advantages of a full 76-byte observer; `hopLoss_eq` shows that `PqxdhRecordLiftIdeal.hopLoss` is the sum of their `ENNReal` images. `observerAt` is the explicit observer `hopObserver` of one index of the hybrid over `hops n budget` indices. `chain_bound` states the chain bound: for every environment, every adversary within its budget and every decision on the permitted view and the final shared cache, `realChains` and `idealChains` differ by at most the sum over the `hops n budget` indices of the Extract-on-`uniform32` and HMAC-PRF advantages of the observers `observerAt`, each with coefficient one. `chain_loss` is the same bound in the `ENNReal` form of `PqxdhRecordLiftIdeal.ChainLiftBool`, with the exact hop losses `hopLoss`.

## Scope

No aliasing or refusal summand arises: every hop changes the mode of one labelled coordinate only (`ChainHop.selected_succ`, `ChainOrder.index_injective`), lookups route by label (`ChainOrder.lookup_agrees`), and the chain worlds never refuse a callback. These structural reasons are collected in `PqxdhRecordLiftChainAlias`. Query bills of the observers are proved in `PqxdhRecordLiftChainBills`; the delivered target is `PqxdhRecordLiftChainLift`.

## Provenance

New Claude work.

## Validation status

All six statements have exact `#print axioms` guards with `propext`, `Classical.choice` and `Quot.sound`. The module passes the focused single-module check (`coord.sh lean`, `-j1 -M8000`, `timeout 180`) against a resolved mirror of the first prefix of the published `LEAN_PATH` of central `ee7878ee` in front of that published `LEAN_PATH`, and the H-7 source scan (version 3) finds no forbidden name; commands, exit statuses and SHA-256 digests are recorded in `doc/impl/proof-receipts/record-lift-chain.json`. The independent semantic and hygiene reviews of `0f06970f` and the fix pass of their findings are recorded in that receipt; central integration is pending.
