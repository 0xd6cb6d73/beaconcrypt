-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter
/-! The corrected stateful Server build is reified over symbolic material addresses. Repeated pin, reserve, raw seal/hash callbacks, dynamic response encoding and installation remain the literal source trees with the same public platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild
open RegistrationNativeSecretWordMessage (Message ServerState)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativePlatformInterpret (state)
variable {n : Nat} {Platform E A : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

abbrev Spec (n : Nat) := (Message →ₒ Option (Choice n)) + RegistrationNativePlatformEffectCompiler.Spec n

def embed : QueryImpl (RegistrationNativePlatformEffectCompiler.Spec n) (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inr query)

def liftEffects (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A) :
    StateT (PublicState Platform) (OracleComp (Spec n)) A := state embed work

def realize (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (Spec n) (OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n))
  | .inl message => (RegistrationNativePlatformServerFrontendCompiler.Spec n).query
      (.inl (RegistrationNativeSecretWordMessage.eval candidate message))
  | .inr query => (RegistrationNativePlatformServerFrontendCompiler.Spec n).query (.inr query)

variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)

noncomputable def service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : Message) : StateT (PublicState Platform) (OracleComp (Spec n))
      (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) := do
  let selected ← StateT.lift ((Spec n).query (.inl message) : OracleComp (Spec n) _)
  match selected with
  | none => pure (.ok (.Err control))
  | some choice => liftEffects (RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice)

noncomputable def body (handle : Nat) (application : Option (Slice U8)) :
    StateT ServerState (StateT (PublicState Platform) (OracleComp (Spec n)))
      (RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) :=
  RegistrationNativePlatformSecretWordBuildControl.build
    (fun pending => liftEffects (RegistrationNativePlatformServerRestrictedService.adHash pending))
    (fun current => liftEffects (RegistrationNativePlatformServerRestrictedService.pin current))
    (liftEffects (RegistrationNativePlatformBoundCompiler.liftPlatform (RegistrationNativePlatformEffectCompiler.compile reserve)))
    (fun keyId => liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
    (service (n := n) source view failure allocation erased helper sign writer) handle application

omit primitive in
private theorem effects_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A) :
    state (realize (n := n) candidate) (liftEffects work) =
      RegistrationNativePlatformServerFrontendCompiler.liftEffects work := by
  funext before
  change simulateQ (realize (n := n) candidate) (simulateQ embed (work.run before)) = _
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation => simulateQ implementation (work.run before))
  funext query
  simp only [QueryImpl.apply_compose, embed, simulateQ_spec_query, realize,
    RegistrationNativePlatformServerFrontendCompiler.embed]

private theorem service_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (message : Message) :
    state (realize (n := n) candidate) (service (n := n) source view failure allocation erased helper sign writer control initial message) =
      RegistrationNativePlatformServerFrontendCompiler.service (n := n) source view failure allocation erased helper sign writer
        control initial (RegistrationNativeSecretWordMessage.eval candidate message) := by
  funext before
  change simulateQ (realize (n := n) candidate)
    ((service (n := n) source view failure allocation erased helper sign writer control initial message).run before) =
      (RegistrationNativePlatformServerFrontendCompiler.service (n := n) source view failure allocation erased helper sign writer
        control initial (RegistrationNativeSecretWordMessage.eval candidate message)).run before
  simp only [service, RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, bind_map_left, simulateQ_bind, simulateQ_spec_query, realize]
  apply bind_congr
  intro selected
  cases selected with
  | none => simp only [StateT.run_pure, simulateQ_pure]
  | some choice => exact congrFun (effects_source candidate _) before

/-- The new symbolic body evaluates to the exact current source compiler with an explicit AD-hash leaf, with no callback or allocator law supplied as a premise. -/
theorem body_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (handle : Nat) (application : Option (Slice U8))
    (before : ServerState) (previous : PublicState Platform) :
    Prod.map (Prod.map id (ServerState.eval candidate)) id <$>
      simulateQ (realize (n := n) candidate) (((body (n := n) source view failure allocation erased helper sign writer reserve handle application).run before).run previous) =
      (simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run (before.eval candidate))).run previous := by
  have mapped := RegistrationNativePlatformSecretWordBuildControl.map_build
    (fun pending => liftEffects (RegistrationNativePlatformServerRestrictedService.adHash pending))
    (fun current => liftEffects (RegistrationNativePlatformServerRestrictedService.pin current))
    (liftEffects (RegistrationNativePlatformBoundCompiler.liftPlatform (RegistrationNativePlatformEffectCompiler.compile reserve)))
    (fun keyId => liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
    (service (n := n) source view failure allocation erased helper sign writer)
    (RegistrationNativePlatformBuildInterpret.state_hom (State := PublicState Platform) (realize (n := n) candidate))
    handle application before
  have mappedRun := congrArg (fun action => action.run previous) mapped
  simp only [state, StateT.run] at mappedRun
  have sourceEq := RegistrationNativePlatformSecretWordBuildControl.build_source candidate
    (fun pending => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformServerRestrictedService.adHash pending))
    (fun current => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformServerRestrictedService.pin current))
    (RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformBoundCompiler.liftPlatform (RegistrationNativePlatformEffectCompiler.compile reserve)))
    (fun keyId => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
    (RegistrationNativePlatformServerFrontendCompiler.service (n := n) source view failure allocation erased helper sign writer)
    (fun control initial message => RegistrationNativePlatformServerFrontendCompiler.service (n := n) source view failure allocation erased helper sign writer
      control initial (RegistrationNativeSecretWordMessage.eval candidate message))
    (fun _ _ _ => rfl) handle application before
  have sourceRun := congrArg (fun action => action.run previous) sourceEq.symm
  rw [StateT.run_map] at sourceRun
  have mappedObservation := congrArg (fun action => Prod.map (Prod.map id (ServerState.eval candidate)) id <$> action) mappedRun
  simp only [effects_source, service_source] at mappedObservation
  have bodyEq : Prod.map (Prod.map id (ServerState.eval candidate)) id <$>
      simulateQ (realize (n := n) candidate) (((body (n := n) source view failure allocation erased helper sign writer reserve handle application).run before).run previous) =
      ((RegistrationNativePlatformServerMaterialFrontend.build
        (fun pending => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformServerRestrictedService.adHash pending))
        (fun current => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformServerRestrictedService.pin current))
        (RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformBoundCompiler.liftPlatform (RegistrationNativePlatformEffectCompiler.compile reserve)))
        (fun keyId => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
        (RegistrationNativePlatformServerFrontendCompiler.service (n := n) source view failure allocation erased helper sign writer)
        handle application).run (before.eval candidate)).run previous := by
    simpa only [body, StateT.run] using mappedObservation.trans sourceRun
  have interpreted := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformServerFrontendProgram.interpret
      (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reserve)
      handle application (before.eval candidate)).symm
  exact bodyEq.trans (by simpa only [RegistrationNativePlatformServerFrontendCompiler.target] using interpreted)

omit primitive in
def nativeEmbedding {KemSK : Type} : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n)
    (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK))
  | .inl message => RegistrationNativePlatformBeaconMaterialInterpreter.demand message
  | .inr (.inl query) => RegistrationBeaconReferenceCompiler.effect query
  | .inr (.inr coin) => RegistrationBeaconReferenceCompiler.effect (.inl coin)

omit primitive in
def wordEmbedding {KemSK : Type} : QueryImpl (Spec n) (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK))
  | .inl message => RegistrationNativeSecretWordInterface.demand message
  | .inr (.inl query) => RegistrationNativeSecretWordInterface.effect query
  | .inr (.inr coin) => RegistrationNativeSecretWordInterface.effect (.inl coin)

omit primitive in
/-- Every actual local build leaf has the same checked interpretation; only the private demand address is evaluated. -/
theorem checked_embedding {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    (RegistrationNativeSecretWordChecked.native (n := n) (KemSK := KemSK) setup.source inside candidate
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) ∘ₛ nativeEmbedding) ∘ₛ realize candidate =
      RegistrationNativeSecretWordChecked.implementation (n := n) (KemSK := KemSK) setup.source inside candidate
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) ∘ₛ wordEmbedding := by
  funext query
  cases query with
  | inl message =>
    simp only [QueryImpl.apply_compose, realize, simulateQ_spec_query, nativeEmbedding, wordEmbedding,
      RegistrationNativePlatformBeaconMaterialInterpreter.demand, RegistrationNativeSecretWordChecked.native,
      RegistrationNativeSecretWordServerSource.realize, RegistrationNativeSecretWordInterface.demand,
      RegistrationNativeSecretWordChecked.implementation]
    exact RegistrationNativeSecretWordCheckedInput.material_literal_eval setup.source inside setup.joint setup.dh seed scalar candidate message
  | inr query => cases query with
    | inl query =>
      simp only [QueryImpl.apply_compose, realize, simulateQ_spec_query, nativeEmbedding, wordEmbedding]
      simpa only [simulateQ_spec_query] using RegistrationNativeSecretWordCheckedMaterial.effects (n := n) (KemSK := KemSK)
        setup.source inside candidate (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        ((PqxdhRecordLiftInterface.EnvEffects n).query query : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _)
    | inr coin =>
      simp only [QueryImpl.apply_compose, realize, simulateQ_spec_query, nativeEmbedding, wordEmbedding]
      simpa only [simulateQ_spec_query] using RegistrationNativeSecretWordCheckedMaterial.effects (n := n) (KemSK := KemSK)
        setup.source inside candidate (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        ((PqxdhRecordLiftInterface.EnvEffects n).query (.inl coin) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _)

/-- The actual stateful source compiler and the new symbolic build agree under the concrete checked local dictionary, including all public platform poststates. -/
theorem checked_source {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (handle : Nat) (application : Option (Slice U8)) (before : ServerState) (previous : PublicState Platform) :
    simulateQ (RegistrationNativeSecretWordChecked.native (n := n) (KemSK := KemSK) setup.source inside candidate
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) ∘ₛ nativeEmbedding)
      ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run (before.eval candidate))).run previous) =
      Prod.map (Prod.map id (ServerState.eval candidate)) id <$>
        simulateQ (RegistrationNativeSecretWordChecked.implementation (n := n) (KemSK := KemSK) setup.source inside candidate
          (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) ∘ₛ wordEmbedding)
          (((body source view failure allocation erased helper sign writer reserve handle application).run before).run previous) := by
  have compared := congrArg (simulateQ (RegistrationNativeSecretWordChecked.native (n := n) (KemSK := KemSK) setup.source inside candidate
    (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) ∘ₛ nativeEmbedding))
    (body_source source view failure allocation erased helper sign writer reserve candidate handle application before previous).symm
  simpa only [simulateQ_map, ← QueryImpl.simulateQ_compose, checked_embedding] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild.body_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild.checked_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild.checked_embedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild.checked_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild.checked_source
