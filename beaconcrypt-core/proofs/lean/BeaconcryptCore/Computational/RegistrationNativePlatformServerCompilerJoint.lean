-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
/-! One actual source-reference execution supplies both the complete literal SourceBuild state and the compiled restricted view. The first marginal retains all actual primitive counters and private metadata; only the second applies the stated security view. No counter equality is imposed between these marginals. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformBoundCompiler (strip)
variable {n : Nat} {E Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

abbrev Result := RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)
abbrev Outcome (n : Nat) (Platform : Type) := (Result × (RegistrationServerMaterialFrontend.State × Local n)) × Platform

def nativeView (roots : RegistrationServerReferenceRestore.Roots) (result : Outcome n Platform) :
    (Result × RegistrationServerFrontendCompiler.State n) × Platform :=
  ((result.1.1, RegistrationNativePlatformServerMaterialState.restore roots result.1.2), result.2)

def clientView (result : Outcome n Platform) :
    (Result × RegistrationServerMaterialFrontend.State) × RegistrationNativePlatformBoundCompiler.State n Platform :=
  ((result.1.1, result.1.2.1), strip (result.1.2.2, result.2))

noncomputable def joint (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : Local n) (previous : Platform) : ProbComp (Outcome n Platform) :=
  ((RegistrationNativePlatformServerMaterialState.close
    (RegistrationNativePlatformServerMaterialFrontend.build
      (RegistrationNativePlatformServerMaterialState.pin RegistrationNativePlatformMldsaProgram.coins)
      (StateT.lift reserve)
      (fun keyId => RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins (.peerPresent keyId))
      (RegistrationNativePlatformServerMaterialState.service RegistrationNativePlatformMldsaProgram.coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        sign helper writer roots) handle application)).run (front, before)).run previous

/-- The first marginal is the complete literal SourceBuild execution on the restored earlier-root capabilities, retaining every native counter, cache, failed prefix and persistent platform poststate. -/
theorem native_marginal (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : Local n) (previous : Platform) :
    nativeView roots <$> joint setup codec view failure allocation erased helper sign writer reserve roots handle application front before previous =
      ((RegistrationNativePlatformSourceBuild.buildSource RegistrationNativePlatformMldsaProgram.coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        reserve sign helper writer handle application).run
        (RegistrationNativePlatformServerMaterialState.restore roots (front, before))).run previous := by
  have actual := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformServerMaterialPin.build RegistrationNativePlatformMldsaProgram.coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
      reserve sign helper writer roots handle application (front, before))
  convert actual using 1
  simp only [joint, StateT.run_map, Prod.map, id_eq]
  rfl

omit primitive in
private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The second marginal of that same source execution is the executable restricted client beside its private root/World interpreter. It applies the named instrumentation view and preserves the actual public control, receipt log and persistent platform state. -/
theorem client_marginal (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : Local n) (previous : Platform) :
    clientView <$> joint setup codec view failure allocation erased helper sign writer reserve roots handle application front before previous =
      (simulateQ (RegistrationNativePlatformServerFrontendCompiler.closed setup.source view failure allocation erased helper sign writer reserve roots)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run (strip (before, previous)) := by
  have actual := RegistrationNativePlatformServerFrontendCompiler.build setup codec view failure allocation erased helper sign writer reserve roots
    handle application front before previous
  simpa only [joint, clientView, RegistrationNativePlatformServerMaterialState.close, StateT.run,
    map_apply, Functor.map_map, Prod.map, id_eq] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint.native_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint.native_marginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint.client_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint.client_marginal
