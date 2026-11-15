-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint
/-! The actual complete four-leaf Server build dictionary uses one physical CTX backend, source state and persistent platform state. It retains actual native accounting and every failed service/pin/reservation path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork publicWork)
open RegistrationNativePlatformCtxLocal (realize)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

/-- The owned transcript-AD continuation uses the same physical CTX hash interpreter as every other private Local hash. -/
noncomputable def adHash (pending : registration.ServerAdHash) :
    M (Local n) Platform RegistrationServerAdHash.Result :=
  RegistrationServerAdHash.runWith (fun request => do
    let digest ← privateWork (RegistrationNativePlatformCtxLocal.effects
      (.inr (.hash (RegistrationInputs.hashBytes request))))
    pure (.Some (RegistrationAuthenticationShared.digestArray digest))) pending

noncomputable def free (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots) :
    QueryImpl RegistrationNativePlatformServerFrontendProgram.Spec (M (Local n) Platform)
  | .adHash pending => adHash pending
  | .pin current => privateWork (RegistrationNativePlatformCtxPin.pin current)
  | .reserve => publicWork reserve
  | .present keyId => privateWork (RegistrationNativePlatformCtxLocal.effects (.inr (.peerPresent keyId)))
  | .service control initial reference => RegistrationNativePlatformCtxStage.service setup codec view failure allocation erased sign helper writer roots control initial reference

omit primitive in
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

omit primitive in
/-- The physical CTX AD leaf reaches the same core continuation, private Local and platform state as the actual source AD leaf. -/
theorem adHash_source (pending : registration.ServerAdHash) (before : Full (Local n) Platform) :
    Prod.map id realize <$> (interpret (adHash (n := n) (Platform := Platform) pending)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformServerMaterialState.adHash RegistrationNativePlatformMldsaProgram.coins pending)).run
        (realize before) := by
  unfold adHash RegistrationNativePlatformServerMaterialState.adHash RegistrationNativePlatformServerCompletion.adHash
    RegistrationNativePlatformServerCompletion.adHashWith RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div =>
    rw [RegistrationNativePlatformCtxRunner.pure_run]
    simp only [RegistrationAgreementNestedState.flatten, StateT.run]
    rfl
  | ok request =>
    simp only [bind_pure_comp]
    have interpret_map {X Y : Type} (f : X → Y) (work : M (Local n) Platform X) :
        interpret (f <$> work) = f <$> interpret work := by
      rw [map_eq_bind_pure_comp, RegistrationNativePlatformCtxRunner.bind_run, map_eq_bind_pure_comp]
      simp only [Function.comp_def, RegistrationNativePlatformCtxRunner.pure_run]
    have flatten_map {X Y : Type} (f : X → Y)
        (work : StateT (Local n) (StateT Platform ProbComp) X) :
        RegistrationAgreementNestedState.flatten (f <$> work) = f <$> RegistrationAgreementNestedState.flatten work := by
      funext state
      simp only [RegistrationAgreementNestedState.flatten, StateT.run, state_map_apply, Functor.map_map, Prod.map_def, id_eq]
    rw [interpret_map, interpret_map, flatten_map, flatten_map, StateT.run_map, StateT.run_map, StateT.run_map,
      StateT.run_map, ← RegistrationNativePlatformCtxPin.capability_source]
    simp only [Functor.map_map, Prod.map_def, id_eq]

theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain) (before : Full (Local n) Platform) :
    Prod.map id realize <$> (interpret (free setup codec view failure allocation erased sign helper writer reserve roots query)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformServerFrontendCompiler.actual setup codec view failure allocation erased helper sign writer reserve roots query)).run (realize before) := by
  cases query with
  | adHash pending => exact adHash_source pending before
  | pin current => exact RegistrationNativePlatformCtxPin.pin_source current before
  | reserve =>
    rw [show free setup codec view failure allocation erased sign helper writer reserve roots .reserve = publicWork reserve from rfl,
      RegistrationNativePlatformCtxRunner.public_run]
    simp only [RegistrationNativePlatformServerFrontendCompiler.actual, RegistrationAgreementNestedState.flatten,
      StateT.run, state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq]
  | present keyId => exact RegistrationNativePlatformCtxPin.capability_source (.peerPresent keyId) before
  | service control initial reference => exact RegistrationNativePlatformCtxStage.service_source setup codec view failure allocation erased sign helper writer roots control initial reference before

/-- Every adaptive complete build prefix retains the exact reached source Local, private cache/counters and public platform state. -/
theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A) (before : Full (Local n) Platform) :
    Prod.map id realize <$> (interpret (simulateQ (free setup codec view failure allocation erased sign helper writer reserve roots) work)).run before =
      (RegistrationAgreementNestedState.flatten
        (simulateQ (RegistrationNativePlatformServerFrontendCompiler.actual setup codec view failure allocation erased helper sign writer reserve roots) work)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.simulate]
  have same := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun query => interpret (free setup codec view failure allocation erased sign helper writer reserve roots query))
    (RegistrationAgreementNestedState.implementation (RegistrationNativePlatformServerFrontendCompiler.actual setup codec view failure allocation erased helper sign writer reserve roots))
    realize (query_source setup codec view failure allocation erased sign helper writer reserve roots) work before
  rw [RegistrationAgreementNestedState.program] at same
  exact same

/-- The exact complete extracted Server build is obtained from the same physical CTX execution, restoring only the earlier private root capability. No codec, writer, or whole-build correctness is a premise. -/
theorem build_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : Full (Local n) Platform) :
    (fun result => ((result.1.1, RegistrationNativePlatformServerMaterialState.restore roots
      (result.1.2, (realize result.2).1)), (realize result.2).2)) <$>
      (interpret (simulateQ (free setup codec view failure allocation erased sign helper writer reserve roots)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front))).run before =
      ((RegistrationNativePlatformSourceBuild.buildSource RegistrationNativePlatformMldsaProgram.coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        reserve sign helper writer handle application).run
        (RegistrationNativePlatformServerMaterialState.restore roots (front, (realize before).1))).run (realize before).2 := by
  have coupled := congrArg (fun distribution =>
    (fun (result : (RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × RegistrationServerMaterialFrontend.State) × (Local n × Platform)) =>
      ((result.1.1, RegistrationNativePlatformServerMaterialState.restore roots (result.1.2, result.2.1)), result.2.2)) <$> distribution)
    (complete setup codec view failure allocation erased sign helper writer reserve roots
      ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front) before)
  conv at coupled =>
    rhs
    rw [RegistrationNativePlatformServerFrontendProgram.interpret]
  have actual := RegistrationNativePlatformServerCompilerJoint.native_marginal setup codec view failure allocation erased helper sign writer reserve roots
    handle application front (realize before).1 (realize before).2
  simp only [Functor.map_map, Prod.map_def, id_eq] at coupled
  apply coupled.trans
  convert actual using 1
  simp only [RegistrationNativePlatformServerCompilerJoint.nativeView,
    RegistrationNativePlatformServerCompilerJoint.joint, RegistrationNativePlatformServerMaterialState.close,
    RegistrationAgreementNestedState.flatten, RegistrationNativePlatformServerFrontendCompiler.actual,
    StateT.run, state_map_apply, Functor.map_map, Prod.map_def, id_eq]
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.adHash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxFrontend.adHash_source
