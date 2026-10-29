-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordSourceProgram
import BeaconcryptCore.Computational.RegistrationNativeWorldView
import BeaconcryptCore.Computational.RegistrationWorldRecords

/-! Actual SDK Server first-record callbacks retain all protocol/record state and the shared World while differing from the locally evaluated source program only in their native-call instrumentation. The view omits that map, the separately billed Env coin ledger and the chronological record-kind log; the underlying source still retains all three for their separate bills. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerRecordWorldSource
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {Auxiliary ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def project (before : RegistrationWorldAgreement.State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  { before with recordRequests := [], world := (RegistrationNativeWorldView.project before.world.1, before.world.2) }

noncomputable def target (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    QueryImpl RegistrationRecordPrimitives.Spec (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) :=
  fun query before => (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
    (simulateQ PqxdhRecordLiftWorld.effects
      (RegistrationServerRecordSourceProgram.native source writer query)).run before.world.1

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Each actual first-record callback has the exact native source reply and complete state after the stated instrumentation view. -/
theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : RegistrationRecordPrimitives.Request) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (RegistrationWorldRecords.handler setup codec request).run before =
      (target setup.source codec.frameWrite request).run (project before) := by
  cases request with
  | rootKdf request => rfl
  | initialKdf request => rfl
  | ratchetKdf request => rfl
  | «seal» request => rfl
  | write request => cases request <;> rfl
  | openAead request => rfl
  | hash transcript =>
      have same := congrArg (fun distribution => (fun result =>
        (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1),
          { project before with world := (result.2, before.world.2) })) <$> distribution)
        (RegistrationNativeWorldView.hash (PqxdhRefinement.absBytes transcript.bytes) before.world.1)
      simp only [RegistrationWorldRecords.handler, RegistrationWorldRecords.shared,
        RegistrationRecordPrimitives.callbacks, RegistrationAuthenticationShared.callbacks,
        RegistrationServerRecordSourceProgram.native, RegistrationRawSealBridge.nativeAdapter,
        RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
        RegistrationBoundSourceCompiler.rawCallbacks, RegistrationBoundSourceCompiler.sharedCompiler,
        RegistrationRawSealBridge.Spec, MldsaSharedNative.authLift,
        simulateQ_map, simulateQ_spec_query,
        bind_pure_comp,
        target, StateT.run, Functor.map_map, Prod.map_def, id_eq, project,
        RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
        RegistrationWorldCoinCompiler.eraseCoin, state_map_apply, PqxdhDeploymentEnvironment.request] at same ⊢
      exact same

/-- Arbitrary adaptive extracted Server record programs use the same full semantic World and optional source results. -/
theorem program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (simulateQ (RegistrationWorldRecords.handler setup codec) work).run before =
      (simulateQ (target setup.source codec.frameWrite) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query setup codec) work before

private theorem target_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : RegistrationRecordPrimitives.Request)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    (target source writer query).run before =
      (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          (RegistrationServerRecordSourceProgram.native source writer query)).run before.world.1 := rfl

/-- Interpreting the source callbacks threads the current full World and keeps every other local coordinate. -/
theorem target_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp RegistrationRecordPrimitives.Spec Value)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    (simulateQ (target source writer) work).run before =
      (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          (simulateQ (RegistrationServerRecordSourceProgram.native source writer) work)).run before.world.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, target_run,
        bind_map_left, ih, map_bind]

/-- The actual initial64/ongoing76 Server controller has the bound108 public-initial program on the same semantic World and real source output. -/
theorem initial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (pending : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : pending.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      (simulateQ (RegistrationWorldRecords.handler setup codec) (RegistrationServerRecordExecutor.fromInitial pending)).run before =
      (fun result => (result.1, { project before with world := (result.2, before.world.2) })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source codec.frameWrite)
            (simulateQ RegistrationRawSealBridge.nativeAdapter
              (RegistrationBoundKeySchedule.factored (RegistrationBoundKeySchedule.publicInitial pending)
                (PqxdhServerAuthKeySchedule.fromRoot setup.source root))))).run
          (RegistrationNativeWorldView.project before.world.1) := by
  rw [program, target_program, RegistrationServerRecordSourceProgram.initial_factored setup.source codec.frameWrite pending root role]
  rfl

end BeaconcryptCore.Computational.RegistrationServerRecordWorldSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.query
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.target_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.target_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordWorldSource.initial
