# Spike S notes (Milestone B, Server-send half of entry_factor)

Worktree `/tmp/beaconcrypt-authenticated-root-completion` (read-only use). Compile: `flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean <file>`.

## Checkpoint 1 (compiled, no sorry)

`SpikeServerSend.lean` part 1: `Factor := RatchetKdfResponse × RootOutput` (76 + 32 = 108 bytes), `address`, `target` (chain_0 = first32 init), `other` (second32 init), `factor`, `known`, `native_known` (rfl), `resolve`, `Settled`, `settled_native`, `embed`, `native_embed`, `StateSettled`, `embed_settled`, `native_settled`, `publish_settled`, `initial_factor` (direct from `RawCtxSelectedInitialConstructor.source_initial`; the two `initialResponse` definitions are defeq). Compile time ~3.5 s.

Existing reusable infrastructure found (Milestone C / HB-112 Server builder):
- `PqxdhInitialGenericBuilder.candidate`/`candidate_native`/`usedBuild`/`used_native`: generic-kernel Server registration tail, natural in a kernel interpretation, with the single premise `sendRealized`.
- `PqxdhInitialGenericPublication.after_native`, `native`, `publish_native`, `registration_source` (`nativeImpl (RawCtxSourceMaterialLabels.nativeImpl source writer) aux = PqxdhRegistrationProtocolState.registrationImpl source writer aux`, rfl).
- `PqxdhInitialBuilderCut.candidate`/`candidate_source`: build factored at the initializer result.
- `RawCtxSelectedChain.send_source`: discharges `sendRealized` for `nativeKernel target` with `calls := RawCtxSelectedChain.calls source writer (response c (nativeRequest target))`; only the 76-byte step response of chain_0 is used.
- `RawCtxSelectedInitialConstructor.source_initial`/`from64_initial`: 64-byte initializer = `nativeKernel (concreteChain first32) <$> initial role second32`.

## Checkpoint 2 (compiled, NO sorry; axioms propext, Classical.choice, Quot.sound)

`server_send_factor` proved: for any `aux` over `StateT (SharedState A) ProbComp`,
`simulateQ (registrationImpl source writer aux) (simulateQ nativeAdapter (build source pending root data metadata state)) = factored source writer aux (factor source root) pending data metadata state`, where `factored` never sees root, the 64-byte initializer or chain_0: it runs `genericBuild (RawCtxSelectedChain.calls source writer value.1) aux (RawCtxSelectedInitialConstructor.initial false value.2) pending data metadata (embed state)` and maps the output state by the target-free `resolve`.
New pieces: `cutBuild`/`cut_source`, `genericBuild`/`build_native` (copy of `used_native` for the plain pending path), `send_begin` (copied from StopTagged), `initial_ok`, `send_shape`, `settle_after`, `settle_candidate`, `settle_generic` (settlement: published kernels have both chains known, so `nativeKernel chain` and `resolve` agree on every reachable output). File ~400 lines; compile ~7 s.

## Checkpoint 3 (compiled, NO sorry)

- `prim_send_source`: the chain placeholder holds for ANY lawful monad `m` and ANY primitive handler `prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m` whose KDF branch is the real `RawCtxSourceHkdf.response` (seal branch arbitrary: e.g. seal logging, `StateT _ (OracleComp RootSpec)`). Labels `primLabels` are address-free.
- `address_ratchet`, `concreteChain_bytes`, `factor_bytes`: `absBytes (factor source root).1.bytes = Pqxdh.ratchetOut c (Pqxdh.rootChains c root).1` and `(factor source root).2.toList = (Pqxdh.rootChains c root).2`, i.e. the factor is exactly the design's `f` in ideal-model terms (B8a's interface), using only `source.prefixConsistent`.

## Checkpoint 4 (final; compiled, NO sorry, 574 lines, ~7 s per compile)

Added `root_only_through_factor` (two roots with equal factor give identical complete native builds), `initial_factor_beacon` and `beacon_receive_factor` (the Beacon initializer hides the same first32 and every Beacon raw receive consumes only `(factor source root).1`; one challenge serves both halves). All axioms: propext, Classical.choice, Quot.sound. Compile log: `compile.log`.

## Findings

Placeholder interface (build level): `Factor := RatchetKdfResponse × RootOutput` = (76-byte step response of chain_0, second32 init). chain_0 is `RawCtxSelectedChain.Slot.hidden`, answered by the challenge; the initializer is `RawCtxSelectedInitialConstructor.initial false other`; the root disappears entirely. Existing peers enter via `known`; the output state is mapped by target-free `resolve`, justified by the settlement lemmas. A root sentinel is needed only at game level (RootSpec derive reply is `Option RootOutput`): a sum-typed reply or a dummy root plus a per-session flag.

Transfer: at chain level (B8b) the Server-send orientation is already covered by Milestone C code: `RawCtxSelectedInitialConstructor` (first32 hidden = Server send / Beacon receive; `RawCtxSelectedInitialSecond` is not needed), `RawCtxSelectedChain.send_source`/`receive_source`, `PqxdhInitialGenericBuilder.candidate_native`, `PqxdhInitialGenericPublication.after_native`. At key level (B9b) only partially: `RawCtxSelectedSendCompiler.send_source`/`native_send` and `RawCtxSelectedSealConsumer.sealing`/`selected_fresh_call` compile a selected seal in the Server orientation, but C's whole-builder compile (`PqxdhFirstBeaconRecordCtx.build_rel`) holds only under `KnownSend`, and C's message layer is address-based (`privateTable prior parent target`), which needs a concrete chain_0 address and alias terms. An address-free material layer via `RawCtxChainRealization.send_execute`/`receive_execute` plus `RawCtxSelectedMessageKey.decoded_selected` keeps the design's no-alias claim.

Split/combined oracle: `server_send_factor` quantifies over arbitrary state, pending, payload and aux, so it is independent of the choice; the split variant only adds game-level bookkeeping (placeholder root stored in the pending list across calls).

Re-estimates: B8b 5000-7500 (Server-send build factor measured at ~0.55k spike lines, ~0.8-1.1k production incl. TailSpec-level generalization); B9b 4000-6500 (address-free material layer, selected-seal builder relation, `event_won`).
