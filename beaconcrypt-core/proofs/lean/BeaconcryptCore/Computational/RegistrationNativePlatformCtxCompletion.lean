-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
/-! The literal supplied-pending source completion executes under one physical CTX/backend state. All source KDF markers, failures, raw receipts and installation state remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformCtxLocal (realize attach)
open RegistrationNativePlatformCtxCacheFrame (replace)
open RegistrationNativePlatformCtxCompletionProgram (Spec)
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
  | .records query => privateWork (RegistrationNativePlatformCtxLocal.records setup codec query)
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
  | .records query => RegistrationNativePlatformServerCompletion.records RegistrationNativePlatformMldsaProgram.coins setup codec query
  | .seal query => RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation query
  | .hash query => RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased query
  | .write query => RegistrationNativePlatformSourceBuild.write helper query
  | .signing query => RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign query
  | .encode current => RegistrationNativePlatformSourceBuild.encode writer current
  | .effect query => RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins query

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
  | records query =>
    simpa only [OracleSpec.Range, RegistrationNativePlatformCtxCompletionProgram.Spec, RegistrationNativePlatformCtxCompletionProgram.Reply,
      free, native, RegistrationNativePlatformServerCompletion.records,
      RegistrationNativePlatformServerCompletion.liftNative, RegistrationAgreementNestedState.flatten,
      StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins,
      state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using
      RegistrationNativePlatformCtxLocal.records_source setup codec query before
  | «seal» query => exact RegistrationNativePlatformCtxSeal.sealing_source setup codec view failure allocation query before
  | hash query => exact RegistrationNativePlatformCtxSeal.hash_source setup codec erased query before
  | write query => exact RegistrationNativePlatformCtxWriters.write_source helper query before
  | signing query =>
    cases query with
    | hash request =>
      simpa only [OracleSpec.Range, RegistrationNativePlatformCtxCompletionProgram.Spec, RegistrationNativePlatformCtxCompletionProgram.Reply,
        free, native, RegistrationNativePlatformServerCompletion.outgoing,
        RegistrationNativePlatformServerCompletion.liftNative, RegistrationAgreementNestedState.flatten,
        StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins,
        state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using
        RegistrationNativePlatformCtxSigning.query_source sign (.hash request) before
    | sign request payload digest =>
      simpa only [OracleSpec.Range, RegistrationNativePlatformCtxCompletionProgram.Spec, RegistrationNativePlatformCtxCompletionProgram.Reply,
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

noncomputable def completion (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    M (Local n) Platform (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) :=
  simulateQ (free setup codec view failure allocation erased sign helper writer)
    (RegistrationNativePlatformCtxCompletionProgram.program control pending)

/-- The actual source completion, including its original pending root and all failure outcomes, uses one full physical CTX/platform state. -/
theorem completion_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) (before : Full (Local n) Platform) :
    Prod.map id realize <$> (interpret (completion setup codec view failure allocation erased sign helper writer control pending)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformSourceBuild.finishSource RegistrationNativePlatformMldsaProgram.coins setup codec
          (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
          (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
          sign helper writer control pending)).run (realize before) := by
  have whole := complete setup codec view failure allocation erased sign helper writer
    (RegistrationNativePlatformCtxCompletionProgram.program control pending) before
  conv at whole =>
    rhs
    rw [RegistrationNativePlatformCtxCompletionProgram.interpret]
  simp only [native] at whole
  change Prod.map id realize <$> (interpret (simulateQ (free setup codec view failure allocation erased sign helper writer)
    (RegistrationNativePlatformCtxCompletionProgram.program control pending))).run before = _
  convert whole using 1
  congr 2
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion.completion_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion.completion_source
