-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordWorldSource

/-! The locally evaluated Server record compiler ignores the same private counter coordinates as its concrete SDK source. Its cache/hash/uniform/administrative and semantic World remain literal through every adaptive continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerRecordTargetProjection
open RegistrationServerRecordWorldSource (project target)
variable {n : Nat} {Auxiliary Value : Type}

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Each actual locally evaluated source callback commutes with the stated source instrumentation view. -/
theorem query (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (request : RegistrationRecordPrimitives.Request) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (target hkdf writer request).run before =
      (target hkdf writer request).run (project before) := by
  cases request with
  | rootKdf request => rfl
  | initialKdf request => rfl
  | ratchetKdf request => rfl
  | «seal» request => rfl
  | write request => cases request <;> rfl
  | openAead request => rfl
  | adHash request =>
      have same := congrArg (fun distribution => (fun result =>
        (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1),
          { project before with world := (result.2, before.world.2) })) <$> distribution)
        (RegistrationNativeWorldView.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before.world.1)
      simp only [RegistrationRecordPrimitives.callbacks, RegistrationAuthenticationShared.callbacks,
        RegistrationServerRecordSourceProgram.native, RegistrationRawSealBridge.nativeAdapter,
        RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
        RegistrationBoundSourceCompiler.rawCallbacks, RegistrationBoundSourceCompiler.sharedCompiler,
        RegistrationRawSealBridge.Spec, MldsaSharedNative.authLift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        target, StateT.run, Functor.map_map, Prod.map_def, id_eq, project,
        state_map_apply, PqxdhDeploymentEnvironment.request] at same ⊢
      exact same
  | hash transcript =>
      have same := congrArg (fun distribution => (fun result =>
        (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1),
          { project before with world := (result.2, before.world.2) })) <$> distribution)
        (RegistrationNativeWorldView.hash (PqxdhRefinement.absBytes transcript.bytes) before.world.1)
      simp only [RegistrationServerRecordSourceProgram.native, RegistrationRawSealBridge.nativeAdapter,
        RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
        RegistrationBoundSourceCompiler.rawCallbacks, RegistrationBoundSourceCompiler.sharedCompiler,
        MldsaSharedNative.authLift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        target, StateT.run, Functor.map_map, Prod.map_def, id_eq, project,
        state_map_apply, PqxdhDeploymentEnvironment.request] at same ⊢
      exact same

/-- Arbitrary native record continuations retain the complete same source-view execution. -/
theorem program (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (simulateQ (target hkdf writer) work).run before =
      (simulateQ (target hkdf writer) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query hkdf writer) work before

end BeaconcryptCore.Computational.RegistrationServerRecordTargetProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordTargetProjection.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordTargetProjection.query
/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordTargetProjection.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordTargetProjection.program
