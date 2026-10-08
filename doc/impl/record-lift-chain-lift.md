# The chain lift (item 5)

`PqxdhRecordLiftChainLift` delivers `chain_lift` of the record-lift brief (H-5, item 5) as fixed in stage S1 by `PqxdhRecordLiftIdeal`: `chain_lift` proves `PqxdhRecordLiftIdeal.ChainLiftTarget setup codec route serverKid bounds n hmac (chainReduction setup codec route serverKid bounds n) chainBills` for every setup, codec, route, Server key ID, fresh bounds, slot count `n` and HMAC. It completes the chain track (takeover plan §2 S3, C1-C4). The target is proved as defined; no definition of `PqxdhRecordLiftIdeal` changed.

## Statement

`ChainLiftTarget` is `ChainLiftStatement` with zero aliasing and refusal terms (`noTerm`, decision D3), and `ChainLiftStatement` is the conjunction of a Boolean form and an event form. Under the contract `SourceFullCorrect setup.source hmac`, for every environment `env` with `Frame env startup allowance`, every observation mode, every adversary with `budget.Respects`, and every decision on the permitted view `PqxdhRecordLiftIdeal.View` and the final shared BLAKE2b cache whose coins are bounded by `cost` (Boolean form), or every Boolean event of the view and the cache (event form):

- `ENNReal.ofReal` of the distinguishing advantage between `realChains` and `idealChains` (an absolute difference, so two-sided) is at most the sum over the `hops n budget = (sends + 51 * receives) * (n * 2)` ordered hybrid indices of `hopLoss hmac (chainReduction ... step)`, the Extract-on-`uniform32` advantage plus the HMAC-PRF advantage of one explicit full 76-byte observer, each with coefficient one, plus the zero aliasing and refusal terms;
- every observer makes at most `chainBills.observer input = 2 * programCoins input + 44 + cost` uniform queries (`PqxdhRecordLiftChainBills`).

`chainReduction` maps an environment, a mode, an adversary, a decision, a budget and an index to `PqxdhRecordLiftChainHybrid.observerAt`: the seed-cut observer of `PqxdhRecordLiftGlobalSeedCut` at depth zero and the parent-cut observer of `PqxdhRecordLiftGlobalCut` at positive depth, each built from the actual compiled protocol, the actual source prefix of its hybrid and the decision. `chain_lift_bool` is the Boolean form; `chain_lift` adds the event form through `PqxdhRecordLiftIdeal.chainLiftStatement_of_bool`; `chain_lift_terms` gives the statement with any explicit aliasing and refusal terms (`PqxdhRecordLiftChainAlias.statement_of_target`).

## How it is proved

`PqxdhRecordLiftSeedRelay` and `PqxdhRecordLiftSeedPolicy` identify the seed-cut endpoint with the adjacent mixed policy (C1). `PqxdhRecordLiftChainHop` proves each hop (C2). `PqxdhRecordLiftChainHybrid` shows that index zero is `realChains`, that the terminal index is `idealChains` for every adversary within its budget, and telescopes the hops (C3); `PqxdhRecordLiftChainAlias` records why no aliasing or refusal term arises (C3, D3). `PqxdhRecordLiftChainBills` proves the bills (C4).

## Use

CE-12 uses `RecordAuthLiftStatement` and `RecordLiftStatement`, whose chain part is this target at the decision that ignores the cache (`PqxdhRecordLiftIdeal.recordAuthLiftBool_of_parts`, `recordLiftBool_of_parts`). The CTX track (S4) delivers the CTX parts. The view `View` contains the environment's final state, so the R6 forms (stage S6) can instantiate the decision with the later-quantum post phase.

## Provenance

New Claude work, composed from published record-lift modules (Codex, and Claude's increment A adaptations).

## Validation status

All three statements have exact `#print axioms` guards with `propext`, `Classical.choice` and `Quot.sound`. The module passes the focused single-module check against `/tmp/bc-arc-scratch/items45/chain/leanpath` (central `ee7878ee`). The H-7 source scan (version 3) finds no forbidden name. Independent review and central integration are pending.
