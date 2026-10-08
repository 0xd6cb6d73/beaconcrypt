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

## Deviations from the plan

The chain track follows takeover plan §2 S3 (C1-C4) with four deviations. None changes a definition of `PqxdhRecordLiftIdeal`, adds an assumption or contract, or changes an advantage coefficient.

- An extra module, this one, holds the delivered target. Plan C3 places `chain_lift` in its two modules (`PqxdhRecordLiftChainHybrid`, `PqxdhRecordLiftChainAlias`), but the target needs the bills of C4 and the alias facts of C3, and `PqxdhRecordLiftChainBills` imports the hybrid (it bills `ChainHybrid.observerAt`), so the target sits in a module that imports both.
- The generic supported-prefix lemmas that plan C3 needs for the support-level policy congruence (`lawEq_bind_support`, `reaches_trans`, `reaches_step`, `reaches_final`, `safe_of_reaches`, `safe_mono`, `chain_lookup_present`, `lookup_present`, `present_preserved`, `lookup_absent`, `run_agrees` and `agrees_update`) live in `PqxdhRecordLiftSeedPolicy`, because the seed prefix `seed_prefix` of C1 needs them first. `PqxdhRecordLiftChainHybrid` applies them with the depth bound `MixedWorld.protocol_run_bounds` (from `run_kdf` and `run_depth`) in `terminal_safe` and `chains_terminal`.
- Plan C4 asks for WorldBudget's real cap plus `76 * (S + 51 * R)` and separate `qPrefix`, `qSuffix` and `T` caps at each cut. `PqxdhRecordLiftChainBills` instead bills the prefix and the suffix of a cut with one closed-form whole-run cap `programCoins` each and every lookup at one full 76-byte reply under every policy, which gives `observerBill = 2 * programCoins + 44 + decision`.
- The 32 retained bytes of a seed cut (`ChainBills.seedObserver_total`) are rounded up to the 44 of a parent cut, so that one bill covers every index (`ChainBills.observerAt_total`).

The last two make the bill explicit and proved but not tight (`doc/impl/record-lift-chain-bills.md`).

## Provenance

New Claude work, composed from published record-lift modules (Codex, and Claude's increment A adaptations).

## Validation status

All three statements have exact `#print axioms` guards with `propext`, `Classical.choice` and `Quot.sound`. The module passes the focused single-module check (`coord.sh lean`, `-j1 -M8000`, `timeout 180`) against a resolved mirror of the first prefix of the published `LEAN_PATH` of central `ee7878ee` in front of that published `LEAN_PATH`, and the H-7 source scan (version 3) finds no forbidden name. The independent semantic and hygiene reviews of `0f06970f`, the fix pass of their findings and the confirming review of the fix pass are recorded in `doc/impl/proof-receipts/record-lift-chain.json`; central integration is pending.

Checks of the chain track as a whole are recorded in the same receipt, with commands, exit statuses and SHA-256 digests of sources, oleans and the `LEAN_PATH`. Each of the seven modules (`PqxdhRecordLiftSeedRelay`, `PqxdhRecordLiftSeedPolicy`, `PqxdhRecordLiftChainHop`, `PqxdhRecordLiftChainHybrid`, `PqxdhRecordLiftChainBills`, `PqxdhRecordLiftChainAlias`, this module; 4, 35, 5, 6, 36, 7 and 3 guarded statements, 96 in all) passes its single-module check through `coord.sh lean claude` with `-j1 -M8000` and `timeout 180`, writing its olean into a fresh prefix, and the root import `BeaconcryptCore.lean` passes against the same path, each with exit 0 and an empty log, both at `0f06970f` and after the fix pass of the review. `coord.sh inv recount` (run before `coord.sh inv rehash`) gives `handwritten-lean` 1670, the focused `check-inventory` under `coord.sh lease mem claude @nix` passes (exit 0), and `git diff --check` is clean. The H-7 meta-level guard over the transitive constant closure of the seven modules (276 declared constants, closure 26645 constants) finds no direct and no closure use of a forbidden name; its only classified hits are the twelve structural DH-interface constants reached through `Setup.beaconDomain`, as in increment A and S1. No escape hatch (`sorry`, `admit`, axiom declaration, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`) occurs. No `lake build`, `make verify`, mutation testing, ProVerif or Rust run.
