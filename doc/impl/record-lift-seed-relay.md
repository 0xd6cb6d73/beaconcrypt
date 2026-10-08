# Persistent initial child for the seed-mask continuation

`PqxdhRecordLiftSeedRelay` factors the directional seed-mask continuation of `PqxdhRecordLiftGlobalSeedCut` through one persistent full 76-byte child cell, in the same way as the published `PqxdhRecordLiftChildRelay` does for the parent-chain mask of `PqxdhRecordLiftGlobalMask`. It is stage C1 of the chain track (item 5, takeover plan `/tmp/bc-arc-scratch/items45-takeover/takeover-plan.md` §2 S3) and the first half of the seed-hop identification; `PqxdhRecordLiftSeedPolicy` is the second half.

## Construction

At the first allocation of a selected slot, `GlobalSeedCut` masks one directional half of the 64-byte seed pair (`Mask`: the retained private state, the slot, the direction and the retained opposite half) and runs the original adaptive Protocol client with a supplied full 76-byte child in place of the HKDF output that would read the masked half. `Needs ideal state query` holds exactly for a lookup of a coordinate that is real under the policy `ideal` and that structurally reads the masked half (`GlobalSeedCut.Reads`: same slot, same direction, the direction's initial position). The relay `interpreter` requests the child from the persistent cell of `PqxdhRecordLiftDeferredChild.Spec` only when `Needs` holds and otherwise supplies a fixed unused value; every other uniform query is forwarded literally through `PqxdhRecordLiftChildRelay.coinLift`. The interpreter takes the seed-mask filling input `filling` of `GlobalSeedCut.interpreter` as a parameter.

## Statements

`unused_source` shows that a service outside `Needs` ignores the supplied child through its complete reply and private state. `query_source` and `schedule_source` show that supplying a fixed child to the relay and erasing only the extra cell gives back the complete seed-mask service and the complete adaptive seed-mask run. `deferred_source` combines this with `PqxdhRecordLiftDeferredChild.initial_law`: a persistent child drawn at its first structural read has the same law as one drawn before the run, under every subsequent probabilistic observation (`LazyOracleDiscard.LawEq`), including runs that never read it.

## Scope

The four statements are operational equalities and contextual distribution laws. They add no cryptographic contract, no reachability assumption and no byte inequality. Identifying the relay with the adjacent concrete policy is `PqxdhRecordLiftSeedPolicy`.

## Provenance

Adapted from Codex WIP `a274839204ccf2a7825ff8f42b107c41ba7d7541cacb76927c9f7ed23d3bb908` (a 49-line stub that never compiled). Claude restarted it: the interpreter now carries the seed-mask filling input that `GlobalSeedCut.interpreter` requires (the cause of the stub's three application type mismatches), and `query_source`, `schedule_source` and `deferred_source` were added after the published `PqxdhRecordLiftChildRelay`. Codex's design note is `codex/deployment-record-wip@023b9a81:doc/impl/handover/record-lift-wip/codex-plan-seed-policy.md` (SHA-256 `02cb4c6516c6bc060b1c0eaa715274c54e04a804d206557b6a91fd1109d6f11d`).

## Validation status

All four statements have exact `#print axioms` guards with `propext`, `Classical.choice` and `Quot.sound`. The module passes the focused single-module check (`coord.sh lean`, `-j1 -M8000`, `timeout 180`) against a resolved mirror of the first prefix of the published `LEAN_PATH` of central `ee7878ee` in front of that published `LEAN_PATH`, and the H-7 source scan (version 3) finds no forbidden name; commands, exit statuses and SHA-256 digests are recorded in `doc/impl/proof-receipts/record-lift-chain.json`. The independent semantic and hygiene reviews of `0f06970f` and the fix pass of their findings are recorded in that receipt; central integration is pending.
