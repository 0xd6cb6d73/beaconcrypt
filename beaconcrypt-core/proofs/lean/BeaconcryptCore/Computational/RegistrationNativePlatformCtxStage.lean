-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
/-! Full source Server material service runs as its exact typed tree under one physical CTX/backend state. Actual KDF markers, every source allocation/writer outcome, native signing receipts and installation state remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformCtxLocal (realize attach)
open RegistrationNativePlatformCtxCacheFrame (replace)
open RegistrationNativePlatformCtxStageProgram (Spec)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

noncomputable def free (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (Spec n) (M (Local n) Platform)
  | .mark => modify fun before => RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before)
  | .seal query => RegistrationNativePlatformCtxSeal.sealing setup codec view failure allocation query
  | .hash query => RegistrationNativePlatformCtxSeal.hash setup codec erased query
  | .write query => RegistrationNativePlatformCtxWriters.write helper query
  | .signing query => privateWork (RegistrationNativePlatformCtxSigning.outgoing sign query)
  | .encode current => RegistrationNativePlatformCtxWriters.encode writer current
  | .effect query => privateWork (RegistrationNativePlatformCtxLocal.effects query)

noncomputable def native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (Spec n) (StateT (Local n) (StateT Platform ProbComp))
  | .mark => modify fun before => RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before)
  | .seal query => RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation query
  | .hash query => RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased query
  | .write query => RegistrationNativePlatformSourceBuild.write helper query
  | .signing query => RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign query
  | .encode current => RegistrationNativePlatformSourceBuild.encode writer current
  | .effect query => RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins query

omit primitive in
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (update : S → S) (before : S) :
    (modify update : StateT S m Unit) before = pure ((), update before) := rfl

omit primitive in
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

omit primitive in
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (Spec n).Domain) (before : Full (Local n) Platform) :
    Prod.map id realize <$> (interpret (free setup codec view failure allocation erased sign helper writer query)).run before =
      (RegistrationAgreementNestedState.flatten
        (native setup codec view failure allocation erased sign helper writer query)).run (realize before) := by
  cases query with
  | mark =>
    simp only [free, native, RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      StateT.run, state_modify_apply, state_pure_apply, simulateQ_pure, map_pure,
      realize, attach, replace, RegistrationNativePlatformPrivateKdfState.initialState,
      RegistrationNativePlatformPrivateKdfState.ratchetState, Prod.map_def, id_eq]
  | «seal» query => exact RegistrationNativePlatformCtxSeal.sealing_source setup codec view failure allocation query before
  | hash query => exact RegistrationNativePlatformCtxSeal.hash_source setup codec erased query before
  | write query => exact RegistrationNativePlatformCtxWriters.write_source helper query before
  | signing query =>
    cases query with
    | hash request =>
      simpa only [OracleSpec.Range, RegistrationNativePlatformCtxStageProgram.Spec, RegistrationNativePlatformCtxStageProgram.Reply,
        free, native, RegistrationNativePlatformServerCompletion.outgoing,
        RegistrationNativePlatformServerCompletion.liftNative, RegistrationAgreementNestedState.flatten,
        StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins,
        state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using
        RegistrationNativePlatformCtxSigning.query_source sign (.hash request) before
    | sign request payload digest =>
      simpa only [OracleSpec.Range, RegistrationNativePlatformCtxStageProgram.Spec, RegistrationNativePlatformCtxStageProgram.Reply,
        free, native, RegistrationNativePlatformServerCompletion.outgoing,
        RegistrationNativePlatformServerCompletion.liftNative, RegistrationAgreementNestedState.flatten,
        StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins,
        state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using
        RegistrationNativePlatformCtxSigning.query_source sign (.sign request payload digest) before
  | encode current => exact RegistrationNativePlatformCtxWriters.encode_source writer current before
  | effect query => exact RegistrationNativePlatformCtxWriters.effects_source query before

/-- The whole actual typed source material-service tree retains full native and platform state under physical interpretation. -/
theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (Spec n) A) (before : Full (Local n) Platform) :
    Prod.map id realize <$> (interpret (simulateQ (free setup codec view failure allocation erased sign helper writer) work)).run before =
      (RegistrationAgreementNestedState.flatten
        (simulateQ (native setup codec view failure allocation erased sign helper writer) work)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.simulate]
  have same := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun query => interpret (free setup codec view failure allocation erased sign helper writer query))
    (RegistrationAgreementNestedState.implementation (native setup codec view failure allocation erased sign helper writer))
    realize (query_source setup codec view failure allocation erased sign helper writer) work before
  rw [RegistrationAgreementNestedState.program] at same
  exact same
noncomputable def service (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (roots : RegistrationServerReferenceRestore.Roots)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativeRelatedFamily.Message) :
    M (Local n) Platform (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) :=
  simulateQ (free setup codec view failure allocation erased sign helper writer)
    (RegistrationNativePlatformCtxStageProgram.program control initial
      (PqxdhServerAuthKeySchedule.fromRoot setup.source (roots reference)))

/-- The actual supplied earlier root and full KDF/service prefix execute under the physical hash interpretation with exact complete source state. -/
theorem service_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (roots : RegistrationServerReferenceRestore.Roots)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativeRelatedFamily.Message) (before : Full (Local n) Platform) :
    Prod.map id realize <$> (interpret (service setup codec view failure allocation erased sign helper writer roots control initial reference)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformServerMaterialState.service RegistrationNativePlatformMldsaProgram.coins setup codec
          (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
          (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
          sign helper writer roots control initial reference)).run (realize before) := by
  have whole := complete setup codec view failure allocation erased sign helper writer
    (RegistrationNativePlatformCtxStageProgram.program control initial (PqxdhServerAuthKeySchedule.fromRoot setup.source (roots reference))) before
  simp only [RegistrationNativePlatformCtxStageProgram.interpret, native] at whole
  change Prod.map id realize <$> (interpret (simulateQ (free setup codec view failure allocation erased sign helper writer)
    (RegistrationNativePlatformCtxStageProgram.program control initial (PqxdhServerAuthKeySchedule.fromRoot setup.source (roots reference))))).run before = _
  rw [RegistrationNativePlatformCtxStageProgram.interpret]
  convert whole using 1
  congr 2
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage.service_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxStage.service_source
