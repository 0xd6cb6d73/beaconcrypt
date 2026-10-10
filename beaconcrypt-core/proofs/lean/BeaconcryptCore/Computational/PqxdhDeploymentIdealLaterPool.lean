-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized

/-! LQ-F upstream, unit B1: the logged handlers with the KEM creations reading the challenger's pool. The later ideal game `PqxdhDeploymentIdealLaterGame.idealLaterGame` creates owner `j`'s KEM key pair from entry `j` of the challenger's pool (`PqxdhDeploymentIdealSteps.createPool`), and item 2's logged prephase builds its router reservation from the same pool. CE-11b unit U5 (`PqxdhDeploymentIdealPool`, `PqxdhDeploymentIdealPoolSource`) carried that pool through CE-3's compile lemma and item 2's source layers for the classical game. The later game also keeps the LQ-F ghosts, the finish snapshot and the Server ephemeral log, and the later decision reads them (through the reveal of the post phase), so this module carries the pool through the logged layers of the LQ-F chain.

- Deployment side: `handlerPoolL` (the logged deployment handler of `PqxdhDeploymentLaterServerGame.handler` with the pool create) and `snapPoolL` (its snapshot form, `PqxdhDeploymentLaterServerGame.snapImpl` with the pool create; away from creates it is that handler, `snapPoolL_real`).
- Source14 side: `nativePoolL` (the native logged source14 handler with the pool create) and the compiled handler `compiledPoolL` (CE-3's compiler with the finish pre-read, `PqxdhDeploymentLaterCompile.compileSnapImpl`). A raw accept runs as under the native logged handler (`compiledPoolL_accept`, `compiledPoolL_server`), every other command as the classical pool compiled step with the snapshot capture and the log kept (`nativePoolL_quiet`, `nativePoolL_program_quiet`, `compiledPoolL_quiet`). `step_merge_poolL`, `good_step_poolL` and `compile_simulation_poolL` are `PqxdhDeploymentLaterServerCompile.server_step`, `server_good` and `server_run` with the pool create, from `PqxdhDeploymentIdealPool.step_merge_pool` and `good_step_pool`.
- Annotated side: `sourcePoolL` (the logged annotated source14 schedule with the pool create) erases to `nativePoolL` with the same log (`sourcePoolL_native`, `programPool_nativeL`, from `PqxdhDeploymentLaterServerNative.acceptSource_native` and `PqxdhDeploymentIdealPoolSource.sourcePool_native`).
- Item 2's logged commands: `executeWithL` runs a logged program through the logged command compiler, the actual encapsulator and a given interpretation of the private services. Under the reserved services (`PqxdhDeploymentIdealPoolSource.reservedAt`), every source14 request is the logged annotated pool source step (`generic_reservedL` through `query_reserved`; `accept_reservedL` through `PqxdhDeploymentLaterServerInitialized.accept_step`, the accept making no KEM creation by `PqxdhDeploymentLaterServerReserve.step_source`; `query_reservedL`), and so is every embedded source14 program (`program_reservedL`, with the invariant kept by `sourcePoolL_owned` through `sourcePoolL_projection`). `kemCommands_stoppedL`: under item 2's stopped selected-first router at the pool, the logged command program of an embedded source14 program that reads no identity or KEM field and fits the pool is the logged annotated pool source execution (`PqxdhDeploymentIdealPoolSource.kemCommands_stopped` with the log).
- The ideal registration before the cut, on the LQ-F view (`PqxdhDeploymentBackend.laterView`: snapshot, deployment state, log): `realRegAt_view`, `onBase_view`, `idealReg_liftL`, `preStepL` and `preScanL` are `PqxdhDeploymentIdealCut.idealReg_lift`, `preStep` and `preScan` with the ghosts kept: before the cut every request projects to `snapPoolL`.
- The stopped router with identity reveals: `stopped_stepL` and `stopped_programL` are `PqxdhDeploymentIdealPoolSource.stopped_step` and `stopped_program` with only KEM reveals excluded (`kemReveal`); the classical forms also exclude identity reveals, which the compiled LQ-F program issues after its run (terminal identity reads and the Server read).

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` (`good_step_poolL` and `compile_simulation_poolL`, as `PqxdhDeploymentLaterServerCompile.server_good` and `server_run` take them); otherwise the invariants and bounds that the statements carry (CE-3's invariant, item 2's pool ownership, the state before the cut, the stopped router's pool prefix and room). These are program equalities and invariant facts. They charge nothing and make no security claim. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhLiveKemReservation (Pair)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentCompileStep (Inv)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentLater (Snap snapshotAt finishOwner)
open PqxdhDeploymentLaterCompile (compileSnapImpl preRead)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentIdealPool (deploymentPool revealPool compiledPool)
open PqxdhRegistrationJointRevealCosts (sourceKind)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The logged handlers with the pool create -/

section Handlers
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (pool : List (Pair KemSK))

/-- The logged native deployment handler with the pool create: a raw accept is the logged accept of `PqxdhDeploymentLaterServerGame.handler`, every other command the native deployment handler with the pool create (`PqxdhDeploymentIdealPool.deploymentPool`) with the log kept. -/
noncomputable def handlerPoolL :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK × Log) ProbComp)
  | .inr (.accept raw) => PqxdhDeploymentLaterServerGame.handler setup codec checks route seed (.inr (.accept raw))
  | query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (deploymentPool setup codec checks route seed pool query).run state.1

/-- The logged snapshot handler with the pool create (`PqxdhDeploymentLaterServerGame.snapImpl` with the pool create): a `finish` first captures the addressed owner's current prekey and one-time fields. -/
noncomputable def snapPoolL :
    QueryImpl Spec (StateT (Snap × (PqxdhDeploymentNative.State KemSK × Log)) ProbComp) := fun query state =>
  (fun result => (result.1, (snapshotAt state.1 state.2.1.native.owners (finishOwner query), result.2))) <$>
    (handlerPoolL setup codec checks route seed pool query).run state.2

/-- The native logged source14 handler with the pool create: a raw accept is the native logged accept with its entry appended (`PqxdhDeploymentLaterServerNative.native`), every other request source14's native handler with the pool create (`PqxdhDeploymentIdealPool.revealPool`) with the log kept. -/
noncomputable def nativePoolL :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (PqxdhRegistrationSchedule.State KemSK × Log) ProbComp)
  | .inl (.inr (.accept raw)) => fun state => (fun result => (result.1.1, (result.2, state.2 ++ [result.1.2]))) <$>
      (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
        raw)).run state.1
  | query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (revealPool setup codec checks seed pool query).run state.1

/-- The compiled handler with the finish snapshot under the native logged pool handler. -/
noncomputable def compiledPoolL :
    QueryImpl Spec (StateT ((Snap × Local) × (PqxdhRegistrationSchedule.State KemSK × Log)) ProbComp) :=
  ((nativePoolL setup codec checks seed pool).mapStateTBase (compileSnapImpl setup codec route)).flattenStateT

/-- A source14 request other than a raw accept runs source14's native handler with the pool create and keeps the log. -/
theorem nativePoolL_quiet (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3) (state : PqxdhRegistrationSchedule.State KemSK)
    (log : Log) :
    (nativePoolL setup codec checks seed pool query).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$> (revealPool setup codec checks seed pool query).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case accept raw => exact absurd rfl notAccept
    all_goals rfl
  all_goals rfl

/-- A source14 program without a raw accept runs, under the native logged pool handler, as under source14's native handler with the pool create, and keeps the log. -/
theorem nativePoolL_program_quiet {Result : Type}
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (noAccept : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 3) 0)
    (state : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (simulateQ (nativePoolL setup codec checks seed pool) program).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$>
        (simulateQ (revealPool setup codec checks seed pool) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at noAccept
    obtain ⟨allowed, rest⟩ := noAccept
    have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := by
      rcases allowed with free | impossible
      · exact free
      · omega
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [nativePoolL_quiet setup codec checks seed pool query notAccept state log, bind_map_left]
    apply bind_congr
    intro result
    have next := rest result.1
    simp only [notAccept, ite_false] at next
    exact ih result.1 next result.2

/-- The compiled raw accept under the native logged pool handler: one native logged accept on the source14 state, its entry appended to the log and its reply recorded in the compiled program's public log (`PqxdhDeploymentLaterServerCompile.accept_compiled` with the pool handler). -/
theorem compiledPoolL_accept (raw : Pqxdh.Bytes) (snap : Snap) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (compiledPoolL setup codec checks route seed pool (.inr (.accept raw))).run ((snap, copies), (native, log)) =
      (fun result => (result.1.1, ((snap, { copies with log := (PqxdhDeploymentCompile.logReply copies.log
          (.accept raw) result.1.1) }), (result.2, log ++ [result.1.2])))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
          seed raw)).run native := by
  have program : (compileSnapImpl setup codec route (.inr (.accept raw))).run (snap, copies) =
      (fun answer => (answer, (snap, { copies with log := (PqxdhDeploymentCompile.logReply copies.log (.accept raw)
        answer) }))) <$> ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query (.inl (.inr (.accept raw))) :
          OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) := by
    simp only [compileSnapImpl, finishOwner, preRead, compileImpl, PqxdhDeploymentCompile.forwardLogged,
      PqxdhDeploymentCompile.forward, StateT.run, pure_bind, bind_assoc, map_eq_bind_pure_comp]
    rfl
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (nativePoolL setup codec checks seed pool) ((compileSnapImpl setup codec route
      (.inr (.accept raw))).run (snap, copies))).run (native, log) = _
  rw [program, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  change _ <$> (_ <$> ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
    (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
      raw)).run native)) = _
  rw [Functor.map_map, Functor.map_map]

/-- A compiled command other than a raw accept under the native logged pool handler: the pool compiled step (`PqxdhDeploymentIdealPool.compiledPool`) with the snapshot capture on the current owners, and the log kept. -/
theorem compiledPoolL_quiet (query : Spec.Domain) (notAccept : ∀ raw, query ≠ .inr (.accept raw)) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) :
    (compiledPoolL setup codec checks route seed pool query).run ((snap, copies), (native, log)) =
      (fun result => (result.1, ((snapshotAt snap native.owners (finishOwner query), result.2.1), (result.2.2, log)))) <$>
        (compiledPool setup codec checks route seed pool query).run (copies, native) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (nativePoolL setup codec checks seed pool) ((compileSnapImpl setup codec route query).run
      (snap, copies))).run (native, log) = _
  rw [nativePoolL_program_quiet setup codec checks seed pool _
    (PqxdhDeploymentLaterServerCompile.snap_quiet setup codec route query notAccept (snap, copies)) native log]
  change _ = _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (revealPool setup codec checks seed pool) ((compileImpl setup codec route query).run copies)).run native)
  have unfolded : (compileSnapImpl setup codec route query).run (snap, copies) =
      preRead snap (finishOwner query) >>= fun captured =>
        (compileImpl setup codec route query).run copies >>= fun result => pure (result.1, (captured, result.2)) := rfl
  have reads : (simulateQ (revealPool setup codec checks seed pool) (preRead (KemSK := KemSK) snap
      (finishOwner query))).run native = pure (snapshotAt snap native.owners (finishOwner query), native) := by
    rw [← PqxdhDeploymentLaterCompile.preRead_run setup codec checks seed snap (finishOwner query) native]
    cases finishOwner query with
    | none => rfl
    | some index => rfl
  rw [unfolded]
  simp only [simulateQ_bind, StateT.run_bind, reads, pure_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
    Functor.map_map]

/-- A command other than a raw accept runs the native deployment handler with the pool create and keeps the log. -/
theorem handlerPoolL_quiet (query : Spec.Domain) (notAccept : ∀ raw, query ≠ .inr (.accept raw))
    (state : PqxdhDeploymentNative.State KemSK) (log : Log) :
    (handlerPoolL setup codec checks route seed pool query).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$> (deploymentPool setup codec checks route seed pool query).run state := by
  rcases query with coin | command
  · rfl
  · cases command
    case accept raw => exact absurd rfl (notAccept raw)
    all_goals rfl

/-- On a raw accept, the compiled handler under the native logged pool handler is the compiled handler under the native logged handler (`PqxdhDeploymentLaterServerCompile.compiledImpl`): the pool create is not reached. -/
theorem compiledPoolL_server (raw : Pqxdh.Bytes)
    (state : (Snap × Local) × (PqxdhRegistrationSchedule.State KemSK × Log)) :
    (compiledPoolL setup codec checks route seed pool (.inr (.accept raw))).run state =
      (PqxdhDeploymentLaterServerCompile.compiledImpl setup codec checks route seed (.inr (.accept raw))).run state := by
  obtain ⟨⟨snap, copies⟩, native, log⟩ := state
  rw [compiledPoolL_accept, PqxdhDeploymentLaterServerCompile.accept_compiled]

/-- One step of the logged pool compile lemma: under CE-3's merge invariant, merging after the compiled step with the finish snapshot under the native logged pool handler is the logged snapshot step with the pool create from the merged state, with the same log. -/
theorem step_merge_poolL (query : Spec.Domain) (snap : Snap) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) (inv : Inv setup codec copies native) :
    (fun result => (result.1, (result.2.1.1, (merge result.2.1.2 result.2.2.1, result.2.2.2)))) <$>
        (compiledPoolL setup codec checks route seed pool query).run ((snap, copies), (native, log)) =
      (snapPoolL setup codec checks route seed pool query).run (snap, (merge copies native, log)) := by
  by_cases accept : ∃ raw, query = .inr (.accept raw)
  · obtain ⟨raw, rfl⟩ := accept
    rw [compiledPoolL_server, PqxdhDeploymentLaterServerCompile.server_step setup codec checks route seed _ snap copies
      native log inv]
    rfl
  · have notAccept : ∀ raw, query ≠ .inr (.accept raw) := fun raw same => accept ⟨raw, same⟩
    rw [compiledPoolL_quiet setup codec checks route seed pool query notAccept snap copies native log,
      Functor.map_map]
    change _ = (fun result => (result.1, (snapshotAt snap (merge copies native).native.owners (finishOwner query),
      result.2))) <$> (handlerPoolL setup codec checks route seed pool query).run (merge copies native, log)
    rw [handlerPoolL_quiet setup codec checks route seed pool query notAccept,
      PqxdhDeploymentLaterCompile.snapshot_merge,
      ← PqxdhDeploymentIdealPool.step_merge_pool setup codec checks route seed pool query copies native inv,
      Functor.map_map, Functor.map_map]
    rfl

/-- Every compiled step with the finish snapshot under the native logged pool handler keeps CE-3's invariant, under the approved codec contracts. -/
theorem good_step_poolL (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (query : Spec.Domain)
    (state : (Snap × Local) × (PqxdhRegistrationSchedule.State KemSK × Log)) (good : Good setup codec state.1.2 state.2.1)
    (result : Spec.Range query × ((Snap × Local) × (PqxdhRegistrationSchedule.State KemSK × Log)))
    (supported : result ∈ support ((compiledPoolL setup codec checks route seed pool query).run state)) :
    Good setup codec result.2.1.2 result.2.2.1 := by
  by_cases accept : ∃ raw, query = .inr (.accept raw)
  · obtain ⟨raw, rfl⟩ := accept
    rw [compiledPoolL_server] at supported
    exact PqxdhDeploymentLaterServerCompile.server_good setup codec checks route seed phase1 phase2 _ state good result
      supported
  · have notAccept : ∀ raw, query ≠ .inr (.accept raw) := fun raw same => accept ⟨raw, same⟩
    obtain ⟨⟨snap, copies⟩, native, log⟩ := state
    rw [compiledPoolL_quiet setup codec checks route seed pool query notAccept snap copies native log,
      support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact PqxdhDeploymentIdealPool.good_step_pool setup codec checks route seed pool phase1 phase2 query copies native
      good inner member

/-- The logged pool compile lemma: from a state with CE-3's invariant, the compiled program with the finish snapshot under the native logged pool handler, merged at the end, has exactly the distribution of the logged snapshot run with the pool create from the merged state, jointly with the output, the snapshot and the log (`PqxdhDeploymentLaterServerCompile.server_run` with the pool create). -/
theorem compile_simulation_poolL {Result : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (program : OracleComp Spec Result) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (log : Log) (good : Good setup codec copies native) :
    (fun result => (result.1, (result.2.1.1, (merge result.2.1.2 result.2.2.1, result.2.2.2)))) <$>
        (simulateQ (compiledPoolL setup codec checks route seed pool) program).run ((snap, copies), (native, log)) =
      (simulateQ (snapPoolL setup codec checks route seed pool) program).run (snap, (merge copies native, log)) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (fun state => Good setup codec state.1.2 state.2.1)
    (fun state => (state.1.1, (merge state.1.2 state.2.1, state.2.2)))
    (fun query state good result supported =>
      good_step_poolL setup codec checks route seed pool phase1 phase2 query state good result supported)
    (fun query state good => step_merge_poolL setup codec checks route seed pool query state.1.1 state.1.2 state.2.1
      state.2.2 (PqxdhDeploymentCompileInvariant.good_inv setup codec _ _ good))
    program ((snap, copies), (native, log)) good

end Handlers

/-! ### The logged annotated source with the pool create and its erasure -/

section Source
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (seed : IdentitySeed)
  (identityIndex : ℕ) (pool : List (Pair KemSK))

/-- The logged annotated source14 schedule with the pool create: a raw accept is the logged annotated accept with its entry appended (`PqxdhDeploymentLaterServerSource.source`), every other request item 2's annotated pool source (`PqxdhDeploymentIdealPoolSource.sourcePool`) with the log kept. -/
noncomputable def sourcePoolL :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (PqxdhRegistrationJointSchedule.State KemSK × Log) ProbComp)
  | .inl (.inr (.accept raw)) => fun state => (fun result => (result.1.1, (result.2, state.2 ++ [result.1.2]))) <$>
      (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks
        seed identityIndex raw)).run state.1
  | query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks seed identityIndex pool query).run state.1

/-- A source14 request other than a raw accept runs item 2's annotated pool source and keeps the log. -/
theorem sourcePoolL_quiet (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (log : Log) :
    (sourcePoolL setup codec checks seed identityIndex pool query).run (state, log) =
      (fun result => (result.1, (result.2, log))) <$>
        (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks seed identityIndex pool query).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case accept raw => exact absurd rfl notAccept
    all_goals rfl
  all_goals rfl

/-- Erasing the private service annotations of one logged annotated pool step gives the native logged pool step, with the same reply and log. -/
theorem sourcePoolL_native (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, (PqxdhRegistrationJointSchedule.source result.2.1, result.2.2))) <$>
        (sourcePoolL setup codec checks seed identityIndex pool query).run (state, log) =
      (nativePoolL setup codec checks seed pool query).run (PqxdhRegistrationJointSchedule.source state, log) := by
  by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
  · obtain ⟨raw, rfl⟩ := accept
    change (fun result => (result.1, (PqxdhRegistrationJointSchedule.source result.2.1, result.2.2))) <$>
        ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
          (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec
            checks seed identityIndex raw)).run state) =
      (fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
          raw)).run (PqxdhRegistrationJointSchedule.source state)
    rw [PqxdhRegistrationSchedule.onShared_run,
      show PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw
          (PqxdhRegistrationJointSchedule.source state).shared =
        (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run state.shared from rfl,
      ← PqxdhDeploymentLaterServerNative.acceptSource_native setup codec checks seed identityIndex raw
        (state.pool, state.shared)]
    simp only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, Functor.map_map]
    rfl
  · have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := fun kind => by
      obtain ⟨raw, same⟩ := PqxdhDeploymentLaterServerNative.kind_accept query kind
      exact accept ⟨raw, same⟩
    rw [sourcePoolL_quiet setup codec checks seed identityIndex pool query notAccept state log,
      nativePoolL_quiet setup codec checks seed pool query notAccept, Functor.map_map,
      ← PqxdhDeploymentIdealPoolSource.sourcePool_native setup codec checks seed identityIndex pool query state,
      Functor.map_map]

/-- The whole logged annotated pool source execution erases to the native logged pool execution, with the same result and log. -/
theorem programPool_nativeL {Result : Type}
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, (PqxdhRegistrationJointSchedule.source result.2.1, result.2.2))) <$>
        (simulateQ (sourcePoolL setup codec checks seed identityIndex pool) program).run (state, log) =
      (simulateQ (nativePoolL setup codec checks seed pool) program).run (PqxdhRegistrationJointSchedule.source state,
        log) := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← sourcePoolL_native setup codec checks seed identityIndex pool query state log, bind_map_left]
      exact bind_congr fun result => ih result.1 result.2.1 result.2.2

end Source

/-! ### The logged commands under the reserved services -/

section Reserved
open PqxdhRegistrationJointGeneratedFinish (EncodedState encodeState)
open PqxdhDeploymentIdealPoolSource (reservedAt PoolOwned executeWith)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The logged command run of a logged-source program under the actual encapsulator and a given interpretation of the private identity and KEM services, from an encoded state and a log (`PqxdhDeploymentLaterServerInitialized.execute` with `service`). -/
noncomputable def executeWithL {Result : Type}
    (service : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (StateT (PqxdhLiveKemBirth.State KemSK) ProbComp))
    (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) Result) (state : EncodedState KemSK) (log : Log) :
    ProbComp (Result × (EncodedState KemSK × Log)) :=
  (fun result => (result.1.1.1, (⟨result.2, result.1.2, result.1.1.2.1⟩, result.1.1.2.2))) <$>
    (simulateQ service (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work state.owners log
        state.shared))).run state.pool

/-- Sequencing for `executeWithL`. -/
theorem executeWithL_bind {Result Next : Type}
    (service : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (StateT (PqxdhLiveKemBirth.State KemSK) ProbComp))
    (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) Result)
    (next : Result → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) Next) (state : EncodedState KemSK)
    (log : Log) :
    executeWithL setup codec checks service identityIndex publicIdentity (work >>= next) state log =
      (executeWithL setup codec checks service identityIndex publicIdentity work state log >>= fun result =>
        executeWithL setup codec checks service identityIndex publicIdentity (next result.1) result.2.1 result.2.2) := by
  simp only [executeWithL, PqxdhDeploymentLaterServerCommands.run_bind, simulateQ_bind, StateT.run_bind, map_bind,
    bind_map_left]

/-- A source14 request other than a raw accept, under the reserved services: the logged command step is item 2's annotated pool source step with the log kept (`PqxdhDeploymentIdealPoolSource.query_reserved`). -/
theorem generic_reservedL (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (log : Log) (owned : PoolOwned seed identityIndex state) :
    executeWithL setup codec checks (reservedAt setup pairs) identityIndex (setup.joint.publicKeys seed)
        ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inl query)) (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (sourcePoolL setup codec checks seed identityIndex pairs query).run (state, log) := by
  have branch : PqxdhDeploymentLaterServerCommands.impl setup codec checks identityIndex (setup.joint.publicKeys seed)
      (.inl query) = fun held => (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex
          (setup.joint.publicKeys seed)) ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run held.1) := by
    rcases query with (coin | request) | read
    case inl.inr =>
      cases request
      case accept raw => exact absurd rfl notAccept
      all_goals rfl
    all_goals rfl
  have exec := PqxdhDeploymentIdealPoolSource.query_reserved setup codec checks seed identityIndex pairs query state
    owned
  simp only [executeWith, PqxdhDeploymentIdealPoolSource.runWith, PqxdhRegistrationJointOpenBackend.compile] at exec
  simp only [executeWithL, PqxdhDeploymentLaterServerCommands.run, simulateQ_spec_query]
  rw [branch, sourcePoolL_quiet setup codec checks seed identityIndex pairs query notAccept, Functor.map_map]
  change _ <$> (simulateQ (reservedAt setup pairs) (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
    (StateT.run ((fun result => (result.1, (result.2, log))) <$> simulateQ (PqxdhRegistrationJointKemEncapsulation.impl
      setup codec checks identityIndex (setup.joint.publicKeys seed)) (StateT.run
        (PqxdhRegistrationJointRevealSchedule.client setup codec query) (encodeState setup state).owners))
      (encodeState setup state).shared))).run (encodeState setup state).pool = _
  rw [StateT.run_map, simulateQ_map, PqxdhRegistrationJointKemEncapsulation.program_actual, simulateQ_map,
    StateT.run_map, Functor.map_map]
  have rhs : (fun a => ((a.1, a.2, log).1, encodeState setup (a.1, a.2, log).2.1, (a.1, a.2, log).2.2)) <$>
      (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks seed identityIndex pairs query).run state =
      (fun result => (result.1, (result.2, log))) <$> ((fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks seed identityIndex pairs query).run state) := by
    rw [Functor.map_map]
  rw [rhs, ← exec, Functor.map_map, Functor.map_map]

/-- On a raw accept, the logged annotated pool source is the logged annotated source. -/
theorem sourcePoolL_accept (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK)) (raw : Pqxdh.Bytes) :
    sourcePoolL setup codec checks seed identityIndex pairs (.inl (.inr (.accept raw))) =
      PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex (.inl (.inl (.inr (.accept raw)))) :=
  rfl

/-- A raw accept under the reserved services: its logged command program creates no KEM key (`PqxdhDeploymentLaterServerReserve.step_source`), so it runs as under the actual services, which is the logged annotated accept (`PqxdhDeploymentLaterServerInitialized.accept_step`). -/
theorem accept_reservedL (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK)) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    executeWithL setup codec checks (reservedAt setup pairs) identityIndex (setup.joint.publicKeys seed)
        ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inl (.inl (.inr (.accept raw))))) (encodeState setup state)
        log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (sourcePoolL setup codec checks seed identityIndex pairs (.inl (.inr (.accept raw)))).run (state, log) := by
  have noCreate := PqxdhDeploymentLaterServerReserve.step_source setup codec checks identityIndex
    (setup.joint.publicKeys seed) (.inl (.inr (.accept raw))) ((encodeState setup state).owners, log)
    (encodeState setup state).shared
  rw [PqxdhDeploymentLaterServerReserve.flat_run, isQueryBoundP_map_iff] at noCreate
  replace noCreate : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      (((PqxdhDeploymentLaterServerCommands.impl setup codec checks identityIndex (setup.joint.publicKeys seed)
        (.inl (.inl (.inr (.accept raw))))).run ((encodeState setup state).owners, log)).run
          (encodeState setup state).shared)).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
    simpa [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind] using noCreate
  have actual : executeWithL setup codec checks (reservedAt setup pairs) identityIndex (setup.joint.publicKeys seed)
      ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inl (.inl (.inr (.accept raw))))) (encodeState setup state)
      log = PqxdhDeploymentLaterServerInitialized.execute setup codec checks identityIndex (setup.joint.publicKeys seed)
        ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inl (.inl (.inr (.accept raw))))) (encodeState setup state)
        log := by
    simp only [executeWithL, PqxdhDeploymentLaterServerInitialized.execute, PqxdhDeploymentLaterServerCommands.run,
      simulateQ_spec_query]
    rw [PqxdhDeploymentIdealPoolSource.reserved_noCreate setup pairs _ noCreate]
  rw [actual, PqxdhDeploymentLaterServerInitialized.accept_step setup codec checks seed identityIndex raw state log owned,
    sourcePoolL_accept]
  rfl

/-- Every source14 request under the reserved services: the logged command step is the logged annotated pool source step. -/
theorem query_reservedL (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (log : Log) (owned : PoolOwned seed identityIndex state) :
    executeWithL setup codec checks (reservedAt setup pairs) identityIndex (setup.joint.publicKeys seed)
        ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inl query)) (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (sourcePoolL setup codec checks seed identityIndex pairs query).run (state, log) := by
  by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
  · obtain ⟨raw, rfl⟩ := accept
    exact accept_reservedL setup codec checks seed identityIndex pairs raw state log owned.1
  · have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := fun kind => by
      obtain ⟨raw, same⟩ := PqxdhDeploymentLaterServerNative.kind_accept query kind
      exact accept ⟨raw, same⟩
    exact generic_reservedL setup codec checks seed identityIndex pairs query notAccept state log owned

/-- Forgetting the log, the logged annotated pool source is item 2's annotated pool source. -/
theorem sourcePoolL_projection (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (log : Log) :
    (fun result => (result.1, result.2.1)) <$> (sourcePoolL setup codec checks seed identityIndex pairs query).run
        (state, log) =
      (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks seed identityIndex pairs query).run state := by
  by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
  · obtain ⟨raw, rfl⟩ := accept
    rw [sourcePoolL_accept]
    exact PqxdhDeploymentLaterServerSource.query_projection setup codec checks seed identityIndex
      (.inl (.inr (.accept raw))) state log
  · have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := fun kind => by
      obtain ⟨raw, same⟩ := PqxdhDeploymentLaterServerNative.kind_accept query kind
      exact accept ⟨raw, same⟩
    rw [sourcePoolL_quiet setup codec checks seed identityIndex pairs query notAccept, Functor.map_map]
    exact id_map _

/-- Every step of the logged annotated pool source keeps the source-side invariant at the pool. -/
theorem sourcePoolL_owned (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (log : Log) (owned : PoolOwned seed identityIndex state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query ×
      (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (supported : result ∈ support ((sourcePoolL setup codec checks seed identityIndex pairs query).run (state, log))) :
    PoolOwned seed identityIndex result.2.1 := by
  have projected : (result.1, result.2.1) ∈ support
      ((PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks seed identityIndex pairs query).run state) := by
    rw [← sourcePoolL_projection setup codec checks seed identityIndex pairs query state log, support_map]
    exact ⟨result, supported, rfl⟩
  exact PqxdhDeploymentIdealPoolSource.query_poolOwned setup codec checks seed identityIndex pairs query state _ owned
    projected

/-- Any source14 program, embedded in the logged source and run by the logged command compiler under the reserved services, has the encoded distribution of its logged annotated pool source execution, with the same log, from a state with the source-side invariant at the pool. -/
theorem program_reservedL {Result : Type} (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) (owned : PoolOwned seed identityIndex state) :
    executeWithL setup codec checks (reservedAt setup pairs) identityIndex (setup.joint.publicKeys seed)
        (simulateQ PqxdhDeploymentLaterServerSource.embed program) (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (simulateQ (sourcePoolL setup codec checks seed identityIndex pairs) program).run (state, log) := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value => simp [executeWithL, PqxdhDeploymentLaterServerCommands.run, encodeState]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhDeploymentLaterServerSource.embed]
      rw [executeWithL_bind, query_reservedL setup codec checks seed identityIndex pairs query state log owned,
        bind_map_left]
      simp only [StateT.run_bind, map_bind]
      apply bind_congr_of_forall_mem_support
      intro result supported
      exact ih result.1 result.2.1 result.2.2
        (sourcePoolL_owned setup codec checks seed identityIndex pairs query state log owned result supported)

/-- Item 2's logged command program of an embedded source14 program with a budget that reads no identity or KEM field and creates no more KEM keys than the pool holds, run by item 2's stopped selected-first router at the pairs from the router state of a prefix pool, is the logged annotated pool source execution read off as the router's reply (with the log), joint identity state and router state (`PqxdhDeploymentIdealPoolSource.kemCommands_stopped` with the log). -/
theorem kemCommands_stoppedL {Result : Type} (selected : ℕ) (seed : IdentitySeed) (identityIndex : ℕ)
    (pairs : List (Pair KemSK)) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) (owned : PoolOwned seed identityIndex state)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix pairs state.pool.2)
    (room : state.pool.2.keys.length + budget (.inl 1) ≤ pairs.length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex (setup.joint.publicKeys seed)
            (simulateQ PqxdhDeploymentLaterServerSource.embed program) (encodeState setup state).owners log
            state.shared))).run).run (state.pool.1, PqxdhDeploymentIdealPoolSource.routerOf state.pool.2) =
      (fun result => (some ((result.1, ((encodeState setup result.2.1).owners, result.2.2)), result.2.1.shared),
          (result.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.1.pool.2))) <$>
        (simulateQ (sourcePoolL setup codec checks seed identityIndex pairs) program).run (state, log) := by
  have classical : ∀ (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : ℕ),
      (PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex (setup.joint.publicKeys seed) program
        (encodeState setup state).owners state.shared).IsQueryBoundP predicate cap →
      (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex (setup.joint.publicKeys seed)
          (simulateQ PqxdhDeploymentLaterServerSource.embed program) (encodeState setup state).owners log
          state.shared)).IsQueryBoundP predicate cap := by
    intro predicate _ cap bound
    rw [← PqxdhRegistrationJointKemEncapsulation.commands_actual, ← PqxdhDeploymentLaterServerCommands.commands_embed
      setup codec checks identityIndex (setup.joint.publicKeys seed) program (encodeState setup state).owners log,
      PqxdhDeploymentLaterServerCommands.commands, simulateQ_map, isQueryBoundP_map_iff] at bound
    exact bound
  have creations := classical _ _ (PqxdhRegistrationJointKemCommands.creations setup codec checks identityIndex
    (setup.joint.publicKeys seed) program budget certified (encodeState setup state).owners state.shared)
  have reveals := PqxdhRegistrationJointOpenCosts.command_program setup codec checks identityIndex
    (setup.joint.publicKeys seed) program budget certified (encodeState setup state).owners state.shared .other
    (by decide)
  simp only [PqxdhRegistrationJointOpenCosts.privateTotal, unreadIdentity, unreadKem] at reveals
  rw [PqxdhDeploymentIdealPoolSource.stopped_program setup selected pairs _ _ creations (classical _ _ reveals)
    state.pool.1 state.pool.2 prefixed room]
  have key : (fun result => (result.1.1.1, ((⟨result.2, result.1.2, result.1.1.2.1⟩ : EncodedState KemSK),
      result.1.1.2.2))) <$> (simulateQ (reservedAt setup pairs) (simulateQ
        (PqxdhRegistrationJointKemEncapsulation.actual setup) (PqxdhDeploymentLaterServerCommands.run setup codec checks
          identityIndex (setup.joint.publicKeys seed) (simulateQ PqxdhDeploymentLaterServerSource.embed program)
          (encodeState setup state).owners log state.shared))).run (state.pool.1, state.pool.2) =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (simulateQ (sourcePoolL setup codec checks seed identityIndex pairs) program).run (state, log) :=
    program_reservedL setup codec checks seed identityIndex pairs program state log owned
  have shape : ∀ (r : ((Result × PqxdhDeploymentLaterServerCommands.Local) × PqxdhServerAuthNative.NativeState KemSK) ×
      PqxdhLiveKemBirth.State KemSK),
      ((some r.1, (r.2.1, PqxdhDeploymentIdealPoolSource.routerOf r.2.2)) :
        Option ((Result × PqxdhDeploymentLaterServerCommands.Local) × PqxdhServerAuthNative.NativeState KemSK) ×
          PqxdhDynamicKemJointSource.State KemSK) =
      ((fun result : Result × (EncodedState KemSK × Log) =>
        ((some ((result.1, (result.2.1.owners, result.2.2)), result.2.1.shared),
          (result.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.1.pool.2)) :
          Option ((Result × PqxdhDeploymentLaterServerCommands.Local) × PqxdhServerAuthNative.NativeState KemSK) ×
            PqxdhDynamicKemJointSource.State KemSK)) ∘
        (fun result => (result.1.1.1, ((⟨result.2, result.1.2, result.1.1.2.1⟩ : EncodedState KemSK),
          result.1.1.2.2)))) r := fun _ => rfl
  refine (congrArg (fun φ => φ <$> (simulateQ (reservedAt setup pairs) (simulateQ
    (PqxdhRegistrationJointKemEncapsulation.actual setup) (PqxdhDeploymentLaterServerCommands.run setup codec checks
      identityIndex (setup.joint.publicKeys seed) (simulateQ PqxdhDeploymentLaterServerSource.embed program)
      (encodeState setup state).owners log state.shared))).run (state.pool.1, state.pool.2)) (funext shape)).trans ?_
  rw [comp_map, key, Functor.map_map]
  rfl

end Reserved

/-! ### The ideal registration before the cut, with the LQ-F ghosts -/

section Pre
open PqxdhDeploymentBackend (XState handlerWith laterView)
open PqxdhDeploymentIdealSlots (detach)
open PqxdhDeploymentIdealSteps (realRegAt liftS IdealCore IdealBk TableState idealReg idealProg)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (PreCut bump)
open PqxdhDeploymentIdealCut (scanCE)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- Away from creates, the logged snapshot pool handler is the logged snapshot handler of the LQ-F game. -/
theorem snapPoolL_real (seed : IdentitySeed) (pool : List (Pair KemSK)) (query : Spec.Domain)
    (notCreate : ∀ pin keyId, query ≠ .inr (.create pin keyId))
    (state : Snap × (PqxdhDeploymentNative.State KemSK × Log)) :
    (snapPoolL setup codec checks route seed pool query).run state =
      (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route seed query).run state := by
  rcases query with coin | command
  · rfl
  · cases command
    case create pin keyId => exact absurd rfl (notCreate pin keyId)
    all_goals rfl

/-- `realRegAt` on the LQ-F view of the extended state is the logged snapshot handler of the LQ-F game. -/
theorem realRegAt_view {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK Bk n) :
    Prod.map id laterView <$> (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run x =
      (PqxdhDeploymentLaterServerGame.snapImpl setup codec checks route created.seed (.inr query.val)).run
        (laterView x) := by
  simp only [realRegAt, StateT.run, Functor.map_map, laterView, PqxdhDeploymentLaterServerGame.snapImpl]
  rfl

/-- A base step of the extended state, on the LQ-F view: the step on the deployment state with the snapshot and the log kept. -/
theorem onBase_view {Bk : Type} {n : ℕ} {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (x : XState KemSK Bk n) :
    Prod.map id laterView <$> (PqxdhDeploymentBackend.onBase step).run x =
      (fun result => (result.1, (x.snap, (result.2, x.log)))) <$> step.run x.base := by
  simp only [PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift, StateT.run, Functor.map_map]
  rfl

variable {count : ℕ} (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- A slot-core command of the ideal registration whose slot program runs a coins-only step projects, on the LQ-F view, to that step's projection. -/
theorem idealReg_liftL (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK (IdealBk TableState) 2)
    (y : XState KemSK IdealCore 2) (step : StateT (XState KemSK IdealCore 2) ProbComp
      (PqxdhRecordLiftInterface.EnvSpec.Range query))
    (target : StateT (Snap × (PqxdhDeploymentNative.State KemSK × Log)) ProbComp
      (PqxdhRecordLiftInterface.EnvSpec.Range query))
    (shape : (idealProg setup codec route checks t p (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)
      created query).run (detach x) = liftS (step.run y))
    (viewed : laterView y = laterView x)
    (stepView : Prod.map id laterView <$> step.run y = target.run (laterView y)) :
    Prod.map id laterView <$> (idealReg setup codec route checks t p created query).run x = target.run (laterView x) := by
  have run := PqxdhDeploymentIdealCut.slotCore_lift (idealProg setup codec route checks t p
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)) PqxdhDeploymentSeedSplit.tableService
    created query x (step.run y) shape
  change Prod.map id laterView <$> (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService
    created query).run x = _
  rw [run, Functor.map_map, ← viewed, ← stepView]
  rfl

/-- One request of the handler with the ideal registration before the cut projects, on the LQ-F view (snapshot, deployment state, log), to the logged snapshot handler with the pool create (`PqxdhDeploymentIdealCut.preStep` with the LQ-F ghosts). -/
theorem preStepL (query : Spec.Domain) (x : XState KemSK (IdealBk TableState) 2) (pre : PreCut x)
    (notSelected : ∀ raw, query = .inr (.accept raw) → x.backend.2.2.accepts ≠ t.accept) :
    Prod.map id laterView <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x =
      (snapPoolL setup codec checks route created.seed (p.pool t) query).run (laterView x) := by
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift]
    rfl
  · cases command with
    | create pin keyId =>
        refine idealReg_liftL setup codec route checks t p created ⟨.create pin keyId, trivial⟩ x (detach x)
          (PqxdhDeploymentIdealSteps.createReg setup (p.pool t) pin keyId) _ rfl rfl ?_
        rw [PqxdhDeploymentIdealSteps.createReg, onBase_view]
        simp only [snapPoolL, handlerPoolL, deploymentPool, StateT.run, Functor.map_map]
        rfl
    | bundle owner =>
        refine idealReg_liftL setup codec route checks t p created ⟨.bundle owner, trivial⟩ x (detach x) _ _ rfl rfl ?_
        rw [realRegAt_view, snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by
          simp)]
    | accept raw =>
        have other := notSelected raw rfl
        refine idealReg_liftL setup codec route checks t p created ⟨.accept raw, trivial⟩ x
          { detach x with backend := { (detach x).backend with accepts := (detach x).backend.accepts + 1 } } _ _
          (PqxdhDeploymentIdealSteps.acceptStep_other setup codec route checks t p created raw (detach x) other) rfl ?_
        rw [realRegAt_view]
        rfl
    | build session payload =>
        refine idealReg_liftL setup codec route checks t p created ⟨.build session payload, trivial⟩ x (detach x) _ _
          (PqxdhDeploymentIdealSteps.buildStep_unmarked setup codec route checks _ created session payload (detach x)
            pre.2) rfl ?_
        rw [realRegAt_view, snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp)]
    | finish owner raw =>
        refine idealReg_liftL setup codec route checks t p created ⟨.finish owner raw, trivial⟩ x (detach x) _ _
          (PqxdhDeploymentIdealSteps.finishStep_real setup codec route checks t p _ created owner raw (detach x)
            (by simp [detach, pre.1])) rfl ?_
        rw [realRegAt_view, snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp)]
    | hmac key message =>
        refine idealReg_liftL setup codec route checks t p created ⟨.hmac key message, trivial⟩ x (detach x) _ _ rfl rfl
          ?_
        rw [realRegAt_view, snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp)]
    | hash bytes =>
        rw [snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp), handlerWith,
          onBase_view]
        simp only [PqxdhDeploymentLaterServerGame.snapImpl, PqxdhDeploymentLaterServerGame.handler, StateT.run,
          Functor.map_map]
        rfl
    | serverSend keyId plaintext =>
        rw [snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp), handlerWith,
          onBase_view]
        simp only [PqxdhDeploymentLaterServerGame.snapImpl, PqxdhDeploymentLaterServerGame.handler, StateT.run,
          Functor.map_map]
        rfl
    | serverRaw raw =>
        rw [snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp), handlerWith,
          onBase_view]
        simp only [PqxdhDeploymentLaterServerGame.snapImpl, PqxdhDeploymentLaterServerGame.handler, StateT.run,
          Functor.map_map]
        rfl
    | beaconSend owner plaintext =>
        rw [snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp), handlerWith,
          onBase_view]
        simp only [PqxdhDeploymentLaterServerGame.snapImpl, PqxdhDeploymentLaterServerGame.handler, StateT.run,
          Functor.map_map]
        rfl
    | beaconRaw owner raw =>
        rw [snapPoolL_real setup codec route checks created.seed (p.pool t) _ (fun _ _ => by simp), handlerWith,
          onBase_view]
        simp only [PqxdhDeploymentLaterServerGame.snapImpl, PqxdhDeploymentLaterServerGame.handler, StateT.run,
          Functor.map_map]
        rfl

/-- The ideal registration before the cut, on the LQ-F view: the scan of a deployment program up to its raw accept at position `index`, run by the handler with the ideal registration from a state before the cut whose accept counter plus `index` is at most the selected ordinal, projects to the scan's run by the logged snapshot handler with the pool create (`PqxdhDeploymentIdealCut.preScan` with the LQ-F ghosts; the backend facts are those of `preScan`). -/
theorem preScanL {X : Type} (work : OracleComp Spec X) (index : ℕ) (x : XState KemSK (IdealBk TableState) 2)
    (pre : PreCut x) (room : x.backend.2.2.accepts + index ≤ t.accept) :
    Prod.map id laterView <$>
        (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
          (scanCE work index)).run x =
      (simulateQ (snapPoolL setup codec checks route created.seed (p.pool t)) (scanCE work index)).run
        (laterView x) := by
  induction work using OracleComp.inductionOn generalizing index x with
  | pure value =>
      rw [PqxdhDeploymentIdealCut.scanCE_pure]
      simp
  | query_bind query next ih =>
      by_cases accept : PqxdhDeploymentCompileBudget.commandKind query = 3
      · rcases query with coin | command
        · exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
        · cases command with
          | accept raw =>
              cases index with
              | zero =>
                  rw [PqxdhDeploymentIdealCut.scanCE_accept_zero]
                  simp
              | succ index =>
                  have other : x.backend.2.2.accepts ≠ t.accept := by omega
                  have step := preStepL setup codec route checks t p created (.inr (.accept raw)) x pre
                    (fun _ same => by cases same; exact other)
                  have kept := (PqxdhDeploymentIdealCut.preStep setup codec route checks t p created (.inr (.accept raw))
                    x pre (fun _ same => by cases same; exact other)).2
                  rw [PqxdhDeploymentIdealCut.scanCE_accept_succ]
                  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                  rw [map_bind, ← step, bind_map_left]
                  refine bind_congr_of_forall_mem_support _ fun reached member => ?_
                  obtain ⟨backend, seeds⟩ := kept reached member
                  have reachedPre : PreCut reached.2 := by
                    simp only [PreCut, backend, bump]
                    exact pre
                  have reachedRoom : reached.2.backend.2.2.accepts + index ≤ t.accept := by
                    simp only [backend, bump]
                    omega
                  exact ih reached.1 index reached.2 reachedPre reachedRoom
          | _ => exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
      · have step := preStepL setup codec route checks t p created query x pre
          (fun raw same => by subst same; exact absurd rfl accept)
        have kept := (PqxdhDeploymentIdealCut.preStep setup codec route checks t p created query x pre
          (fun raw same => by subst same; exact absurd rfl accept)).2
        have same : bump query x.backend = x.backend := by
          rcases query with coin | command
          · rfl
          · cases command with
            | accept raw => exact absurd rfl accept
            | _ => rfl
        rw [PqxdhDeploymentIdealCut.scanCE_other query accept]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        rw [map_bind, ← step, bind_map_left]
        refine bind_congr_of_forall_mem_support _ fun reached member => ?_
        obtain ⟨backend, seeds⟩ := kept reached member
        rw [same] at backend
        have reachedPre : PreCut reached.2 := by
          simp only [PreCut, backend]
          exact pre
        exact ih reached.1 index reached.2 reachedPre (by rw [backend]; exact room)

end Pre

/-! ### The stopped selected-first router with identity reveals -/

section Router
open PqxdhDeploymentIdealPoolSource (reservedAt PoolPrefix routerOf)
variable (setup : Setup baseSpec KemSK)

/-- Whether a private-service request is a KEM reveal (the only request the stopped router answers by a stop besides a creation beyond its reservation). -/
def kemReveal : (PqxdhLiveKemBirth.Spec KemSK).Domain → Bool
  | .inr (.inr (.reveal _)) => true
  | _ => false

/-- One request of the stopped selected-first router at the pairs, from the router state of a prefix pool, is the request under the reserved services followed by the router state of the new pool, for every request but a KEM reveal and within the pool (`PqxdhDeploymentIdealPoolSource.stopped_step`, which also excludes identity reveals). -/
theorem stopped_stepL (selected : ℕ) (pairs : List (Pair KemSK)) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (notReveal : kemReveal query = false)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PoolPrefix pairs pool)
    (room : pool.keys.length + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤ pairs.length) :
    ((PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs query).run).run
        (joint, routerOf pool) =
      (fun result => (some result.1, (result.2.1, routerOf result.2.2))) <$>
        (reservedAt setup pairs query).run (joint, pool) := by
  rcases query with request | (coin | request)
  · simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
      PqxdhLiveKemReservation.reserved, PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
  · simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
      PqxdhLiveKemReservation.reserved, PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
  · cases request with
    | create =>
        have before : pool.keys.length < pairs.length := by
          simpa [PqxdhLiveKemReservation.IsCreate] using room
        have found : pairs[pool.keys.length]? = some pairs[pool.keys.length] :=
          List.getElem?_eq_some_iff.mpr ⟨before, rfl⟩
        simp [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
          PqxdhLiveKemReservation.reserved, PqxdhDynamicKemRouter.source, StateT.run, routerOf, found,
          PqxdhLiveKemBirth.created, PqxdhDynamicKemRouter.record, PqxdhLiveKemBirth.record]
    | decapsulate index ciphertext =>
        have keys : pairs.take pool.keys.length = pool.keys := prefixed.symm
        simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
          PqxdhLiveKemReservation.reserved, PqxdhDynamicKemRouter.source, PqxdhLiveKemBirth.impl,
          PqxdhLiveKemBirth.poolImpl, StateT.run, routerOf, keys]
        cases pool.keys[index]? <;>
          simp [PqxdhDynamicKemRouter.record, PqxdhLiveKemBirth.record, Functor.map_map]
    | reveal index => simp [kemReveal] at notReveal

/-- A private-service program with at most `qCreate` KEM creations within the pool and no KEM reveal, run by item 2's stopped selected-first router at the pairs from the router state of a prefix pool, is its run under the reserved services, with every reply present and the router state of the final pool (`PqxdhDeploymentIdealPoolSource.stopped_program` with identity reveals allowed). -/
theorem stopped_programL {α : Type} (selected : ℕ) (pairs : List (Pair KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (qCreate : ℕ)
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) qCreate)
    (noReveal : client.IsQueryBoundP (fun query => kemReveal (KemSK := KemSK) query = true) 0)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PoolPrefix pairs pool) (room : pool.keys.length + qCreate ≤ pairs.length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        client).run).run (joint, routerOf pool) =
      (fun result => (some result.1, (result.2.1, routerOf result.2.2))) <$>
        (simulateQ (reservedAt setup pairs) client).run (joint, pool) := by
  induction client using OracleComp.inductionOn generalizing qCreate joint pool with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded noReveal
      have notReveal : kemReveal (KemSK := KemSK) query = false := by
        rcases noReveal.1 with absent | impossible
        · simpa using absent
        · exact absurd impossible (Nat.lt_irrefl 0)
      have affordable : pool.keys.length + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤
          pairs.length := by
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind,
        stopped_stepL setup selected pairs query notReveal joint pool prefixed affordable, bind_map_left,
        Option.elim_some]
      apply bind_congr_of_forall_mem_support
      rintro ⟨answer, after⟩ supported
      have step := PqxdhDeploymentIdealPoolSource.reserved_step_prefix setup pairs query joint pool prefixed affordable
        (answer, after) supported
      have nextRoom : after.2.keys.length + (if PqxdhLiveKemReservation.IsCreate query then qCreate - 1 else qCreate) ≤
          pairs.length := by
        rw [step.2]
        split_ifs at affordable ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      exact ih answer _ (bounded.2 answer) (by simpa [notReveal] using noReveal.2 answer) after.1 after.2 step.1 nextRoom

end Router

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.nativePoolL_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.nativePoolL_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.nativePoolL_program_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.nativePoolL_program_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compiledPoolL_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compiledPoolL_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compiledPoolL_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compiledPoolL_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.handlerPoolL_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.handlerPoolL_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compiledPoolL_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compiledPoolL_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.step_merge_poolL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.step_merge_poolL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.good_step_poolL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.good_step_poolL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compile_simulation_poolL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.compile_simulation_poolL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.programPool_nativeL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.programPool_nativeL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.executeWithL_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.executeWithL_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.generic_reservedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.generic_reservedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.accept_reservedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.accept_reservedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.query_reservedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.query_reservedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_projection

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.sourcePoolL_owned

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.program_reservedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.program_reservedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.kemCommands_stoppedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.kemCommands_stoppedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.snapPoolL_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.snapPoolL_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.realRegAt_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.realRegAt_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.onBase_view' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.onBase_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.idealReg_liftL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.idealReg_liftL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.preStepL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.preStepL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.preScanL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.preScanL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.stopped_stepL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.stopped_stepL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.stopped_programL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool.stopped_programL
