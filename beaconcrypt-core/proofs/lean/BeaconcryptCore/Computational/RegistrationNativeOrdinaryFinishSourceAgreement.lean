-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame

/-! The ordinary owner's root preparation returns its translated reference while reconstructing its own actual scalar-dependent native agreement. Only the private reference memo is projected from this comparison; its freshly prepared capability remains available to the later completion theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationNativeOrdinaryFinishSourceFrame (drop)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationBeaconReferenceNativePreparation (restored)
open RegistrationNativePublicOwners (ordinary)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Ordinary materialization forwards the entire actual collection program before its sole preparation query. -/
theorem collect_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar localScalar : ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : EnvState Auxiliary) (before : Private n KemSK) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (ordinary setup localScalar)
          ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env))).run before =
      (RegistrationBeaconReferenceGenericStage.lower setup (trusted setup wire route sign seed selectedScalar)
        (RegistrationBeaconReferenceCompiler.trustedCollect setup owner oneTime authenticated)).run (env, before) := by
  rw [← RegistrationBeaconReferenceCallbacks.collect_lift,
    RegistrationNativeOrdinaryFinishSourceWrapper.trusted_program, ← QueryImpl.simulateQ_compose]
  rfl

/-- The materialized capability and its freshly returned private root reconstruct the complete native collection/root stage for the ordinary scalar. -/
theorem agreement_stage (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar localScalar : ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : EnvState Auxiliary) (before : Private n KemSK) :
    (fun result => (restored result.2.extra.1 authenticated result.1.1, (result.1.2, drop result.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (ordinary setup localScalar)
          ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env))).run before =
      (fun result => (result.1, (result.2.2.1, drop result.2.2.2))) <$>
        (RegistrationBeaconReferenceGenericAgreement.stage setup (trusted setup wire route sign seed selectedScalar) owner oneTime
          (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh seed localScalar)
          authenticated).run (RegistrationNativeRelatedFamily.empty, (env, before)) := by
  rw [RegistrationBeaconReferenceGenericAgreement.stage_run]
  simp only [RegistrationBeaconReferenceCompiler.agreement, StateT.run_bind, simulateQ_bind, map_bind]
  have collected := collect_source setup wire route sign seed selectedScalar localScalar owner oneTime authenticated env before
  rw [← collected, bind_map_left]
  apply bind_congr
  rintro ⟨⟨pending, afterEnv⟩, after⟩
  cases pending with
  | none =>
      simp only [StateT.run_pure, simulateQ_pure, map_pure, restored,
        RegistrationBeaconReferenceRoot.restored, drop]
  | some pending =>
      have actual := RegistrationNativeOrdinaryFinishSourcePreparation.client_source setup wire route sign seed
        selectedScalar localScalar authenticated pending after
      have root := RegistrationNativeSourceRoot.program_value setup.source setup.hmac setup.joint setup.dh seed localScalar
        (RegistrationNativeBeaconRootSource.client authenticated pending) RegistrationNativeRelatedFamily.empty
      rw [← root] at actual
      have mapped := congrArg (fun distribution => (fun result => (result.1, (afterEnv, result.2))) <$> distribution) actual
      simpa only [StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map,
        Functor.map_map, Prod.map_def, id_eq, drop] using mapped

/-- Complete ordinary-owner preparation runs its actual native agreement controller under the same reached World and indexed pool. -/
theorem agreement_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar localScalar : ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (env : EnvState Auxiliary) (before : Private n KemSK) :
    (fun result => (restored result.2.extra.1 authenticated result.1.1, (result.1.2, drop result.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (ordinary setup localScalar)
          ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env))).run before =
      (fun result => (result.1, (result.2.1, drop result.2.2))) <$>
        (simulateQ (RegistrationBeaconReferenceGenericStage.native setup (trusted setup wire route sign seed selectedScalar)
          localScalar owner oneTime) (RegistrationAgreementExecutor.beacon authenticated)).run (env, before) := by
  rw [agreement_stage]
  have native := congrArg (fun distribution => (fun result => (result.1, (result.2.1, drop result.2.2))) <$> distribution)
    (RegistrationBeaconReferenceGenericAgreement.stage_native setup (trusted setup wire route sign seed selectedScalar) seed
      localScalar owner oneTime authenticated coherent (RegistrationNativeRelatedFamily.empty, (env, before)))
  simpa only [Functor.map_map, Prod.map_def, id_eq] using native

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement.collect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement.agreement_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement.agreement_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement.agreement_source
