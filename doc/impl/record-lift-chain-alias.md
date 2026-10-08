# Why the chain lift has no aliasing or refusal term

`PqxdhRecordLiftChainAlias` states, as theorems, the structural reasons of decision D3 of the takeover plan (recorded in `doc/impl/record-lift-ideal.md`): the aliasing and refusal summands of `PqxdhRecordLiftIdeal.ChainLiftStatement` are zero for the chain lift. It is part of stage C3 of the chain track (item 5, takeover plan §2 S3). No contract is used.

## Aliasing

The ordered hybrid replaces labelled callbacks, never byte values. `hops_injective` shows that distinct hops of `PqxdhRecordLiftChainOrder` idealize distinct coordinates, without any byte comparison. `adjacent_agree` and `adjacent_query` show that adjacent hybrids agree, and execute identically on every private state with every reply byte retained, at every private service except the lookup of the hop's own coordinate. Two coordinates whose outputs happen to collide are still separate callbacks, so no collision event appears in the hybrid. Adversary or environment HKDF evaluations at a hidden chain value are not an alias event either: they run inside the explicit observers of `PqxdhRecordLiftChainHop.hopObserver`, which simulate the whole environment, adversary and decision, and are covered by the standard-model Extract-on-`uniform32` and HMAC-PRF advantages (CE's `hmac` is the real HMAC outside the 192-byte zero-salt slice, and ratchet Extract inputs are 32-byte chains, never in that slice).

## Refusal

`kernel_total` restates `PqxdhRecordLiftWorld.hiddenKernel_total`: every hidden kernel constructor is total, so no seed-dependent refusal or fallback kernel exists. `installServer_admission` and `installBeacon_admission` show that a hidden installation of the key-free client is admitted exactly when its control state admits it (an unoccupied peer key ID or a ready owner, and an unused slot for the role), under every reply: the only private request is the allocation, whose reply is unit, so refusal depends on no seed, table or primitive state. The chain worlds therefore never refuse a chain callback, and the hops of `PqxdhRecordLiftChainHop` are exact.

## Explicit summands

`statement_of_target` shows that a chain target with zero aliasing and refusal terms (`ChainLiftTarget`, the `noTerm` instantiation) implies the chain statement with any explicit aliasing and refusal terms. `PqxdhRecordLiftChainLift.chain_lift_terms` applies it to the delivered target.

## Provenance

New Claude work.

## Validation status

All seven statements have exact `#print axioms` guards with `propext`, `Classical.choice` and `Quot.sound`. The module passes the focused single-module check against `/tmp/bc-arc-scratch/items45/chain/leanpath` (central `ee7878ee`). The H-7 source scan (version 3) finds no forbidden name. Independent review (which must confirm decision D3) and central integration are pending.
