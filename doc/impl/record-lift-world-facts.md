# Record-lift stage S5: `record_lift` composition and the ideal-world facts (items 4 and 5)

Stage S5 of the items 4/5 takeover plan (`/tmp/bc-arc-scratch/items45-takeover/takeover-plan.md` §2 S5, decisions D1-D5) composes the delivered lifts into `record_lift` and proves the world-level facts that the common deployment experiment consumes on the ideal record worlds of `PqxdhRecordLiftIdeal` (guide `doc/impl/record-lift-ideal.md`): `OriginStatement` and `BindingStatement` (CE-OR, CE-UKS), `HidingStatement`, `FreshGuessStatement` and `LorStatement` (CE-APP, CE-LOR). Every target is proved as defined on central; no target definition, assumption or contract changes.

## Status

Built by Claude on branch `codex/deployment-record-world` (worktree `/tmp/beaconcrypt-deployment-record-world`, base central `14f51c34`), scratch `/tmp/bc-arc-scratch/items45/world`. New Claude work; nothing is adapted from Codex WIP. Not yet reviewed or integrated.

| Target | Module | State |
| --- | --- | --- |
| `RecordAuthLiftTarget` (integrity `record_lift`) | `PqxdhRecordLiftComposition` | proved (`record_auth_lift`) |
| `RecordLiftTarget`, `CtxLiftTarget` | `PqxdhRecordLiftComposition` | proved with the privacy half as a hypothesis parameter (`record_lift_of_priv`, `ctx_lift_of_priv`); mode O unconditionally (`record_lift_O`) |
| `HidingStatement` | planned `PqxdhRecordLiftHiding` | open |
| `FreshGuessStatement`, `LorStatement` | planned, on top of the hiding coupling | open |
| `OriginStatement`, `BindingStatement` | planned | open |

## `PqxdhRecordLiftComposition` (7 guarded theorems)

`record_auth_lift_bool` applies `PqxdhRecordLiftIdeal.recordAuthLiftBool_of_parts` to `PqxdhRecordLiftChainLift.chain_lift_bool` (item 5) and to the Boolean half of `PqxdhRecordLiftCtxBills.ctxAuthLiftTarget` (the integrity half of item 4). The chain lift is used at the cache-free decision `fun view _ => decision view`, so its observers are exactly the ones `recordAuthLoss` names. `record_auth_lift` adds the event form through `recordAuthLiftStatement_of_bool` and is the delivered target `RecordAuthLiftTarget setup codec route serverKid bounds n hmac fallback (chainReduction ...) (ctxReduction ...) chainBills ctxBills`, for every slot count, HMAC, forgery fallback and setup. `record_auth_lift_terms` gives the same statement for arbitrary alias and refusal terms, from `chain_lift_terms` and `ctxAuthLiftStatement`.

The privacy half `CtxPrivLiftStatement` is not on central yet. `ctx_lift_of_priv` (`CtxLiftTarget`), `record_lift_bool_of_priv` and `record_lift_of_priv` (`RecordLiftTarget`) take it as an explicit hypothesis parameter `privLift` for any privacy reduction family `privacy` and bills `privacyBills`, and use `ctxLiftBool_of_parts` and `recordLiftBool_of_parts`. The parameter is part of the theorem statement, not an assumption or contract: nothing is claimed about the privacy half, and once the privacy track proves `CtxPrivLiftStatement setup codec route serverKid bounds n privacy privacyBills` for its explicit reductions, `record_lift_of_priv ... privacy privacyBills (that proof)` is the full `record_lift` target with no further work. What remains for the full target is exactly that proof. `record_lift_O` states the Boolean bound for observation mode O without the hypothesis: there `idealRecords` is `idealAuth` (`idealRecords_O`) and `recordLoss` has no privacy summand.

Contracts per theorem: `record_auth_lift_bool`, `record_auth_lift`, `record_auth_lift_terms`, `record_lift_bool_of_priv`, `record_lift_of_priv` and `record_lift_O` have `SourceFullCorrect` as the explicit first premise of the target (the chain lift's contract) and use, through `ctxAuthLiftTarget` and `ctxAuthLiftStatement`, functional AEAD correctness (`aead_open_seal`, `aeadSeal_tag_length`), the modified-nonce AEAD IND$ and INT-CTXT games and the HMAC-PRF and Extract-on-`uniform32` games as advantage terms of the losses, and the BLAKE2b random-oracle model as the world model; `ctx_lift_of_priv` uses the CTX part of that list only (no `SourceFullCorrect`). All are on the brief's H-7 list; no new assumption or contract.

## Checks

Per module: a development check with plain `#print axioms` probes, the module check with `-o` into the fresh prefix `/tmp/bc-arc-scratch/items45/world/olean` (a resolved mirror of the first prefix of the published `LEAN_PATH` of central `14f51c34`, without its root olean), the root import, `coord.sh inv recount` before `coord.sh inv rehash`, the focused `check-inventory` under the `@nix` lease, the H-7 source scan (version 3) and the H-7 closure guard over the track's modules, the exact-guard scan and `git diff --check`. The commands, exit statuses and digests are recorded in the receipt `doc/impl/proof-receipts/record-lift-world-facts.json`. The receipt is not named `record-lift-world.json` because that file (and `doc/impl/record-lift-world.md`) already belong to the frozen `PqxdhRecordLiftWorld` increment.
