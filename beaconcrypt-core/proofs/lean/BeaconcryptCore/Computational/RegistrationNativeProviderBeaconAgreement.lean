-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation

/-! The Beacon collector executes the actual provider, including indexed decapsulation, before one private native root step. The generic agreement engine retains the full reached World, live pool, provider state and signing receipts. Only the root-reference memo is projected from the native comparison. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState implementation)
open RegistrationNativeProviderBeaconPreparation (drop)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner trustedLift)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {n : Nat} {ι KemSK ProviderState Auxiliary : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def trusted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK)
      (StateT (NativeState n KemSK ProviderState) ProbComp) :=
  implementation setup wire route sign seed scalar provider false ∘ₛ trustedLift

/-- The selected or ordinary owner collects through the same actual provider; local materialization changes no trusted callback. -/
theorem collect_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : EnvState Auxiliary)
    (before : NativeState n KemSK ProviderState) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env))).run before =
      (RegistrationBeaconReferenceGenericStage.lower setup
        (trusted setup wire route sign seed selectedScalar provider)
        (RegistrationBeaconReferenceCompiler.trustedCollect setup owner oneTime authenticated)).run (env, before) := by
  rw [← RegistrationBeaconReferenceCallbacks.collect_lift]
  cases localScalar with
  | none =>
      simp only [adapt, simulateQ_id']
      rw [← QueryImpl.simulateQ_compose]
      rfl
  | some scalar =>
      rw [adapt, RegistrationNativeOrdinaryFinishSourceWrapper.trusted_program,
        ← QueryImpl.simulateQ_compose]
      rfl

/-- Fresh returned references reconstruct the complete literal native root stage, with the provider retained at every collection callback. -/
theorem agreement_stage (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : EnvState Auxiliary)
    (before : NativeState n KemSK ProviderState) :
    (fun result => (restored result.2.1.extra.1 authenticated result.1.1, (result.1.2, drop result.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env))).run before =
      (fun result => (result.1, (result.2.2.1, drop result.2.2.2))) <$>
        (RegistrationBeaconReferenceGenericAgreement.stage setup
          (trusted setup wire route sign seed selectedScalar provider) owner oneTime
          (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh seed
            (localScalar.getD selectedScalar)) authenticated).run
              (RegistrationNativeRelatedFamily.empty, (env, before)) := by
  rw [RegistrationBeaconReferenceGenericAgreement.stage_run]
  simp only [RegistrationBeaconReferenceCompiler.agreement, StateT.run_bind, simulateQ_bind, map_bind]
  have collected := collect_source setup wire route sign seed selectedScalar localScalar provider owner oneTime authenticated env before
  rw [← collected, bind_map_left]
  apply bind_congr
  rintro ⟨⟨pending, afterEnv⟩, after⟩
  cases pending with
  | none =>
      simp only [StateT.run_pure, simulateQ_pure, map_pure, restored,
        RegistrationBeaconReferenceRoot.restored, drop]
  | some pending =>
      have actual := RegistrationNativeProviderBeaconPreparation.client_source setup wire route sign seed
        selectedScalar localScalar provider authenticated pending after
      have root := RegistrationNativeSourceRoot.program_value setup.source setup.hmac setup.joint setup.dh seed
        (localScalar.getD selectedScalar) (RegistrationNativeBeaconRootSource.client authenticated pending)
          RegistrationNativeRelatedFamily.empty
      rw [← root] at actual
      have mapped := congrArg (fun distribution => (fun result => (result.1, (afterEnv, result.2))) <$> distribution) actual
      simpa only [StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map,
        Functor.map_map, Prod.map_def, id_eq, drop] using mapped

/-- The actual provider-dependent collector and native agreement controller agree on the complete retained state. -/
theorem agreement_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (env : EnvState Auxiliary) (before : NativeState n KemSK ProviderState) :
    (fun result => (restored result.2.1.extra.1 authenticated result.1.1, (result.1.2, drop result.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env))).run before =
      (fun result => (result.1, (result.2.1, drop result.2.2))) <$>
        (simulateQ (RegistrationBeaconReferenceGenericStage.native setup
          (trusted setup wire route sign seed selectedScalar provider)
          (localScalar.getD selectedScalar) owner oneTime) (RegistrationAgreementExecutor.beacon authenticated)).run (env, before) := by
  rw [agreement_stage]
  have native := congrArg (fun distribution => (fun result => (result.1, (result.2.1, drop result.2.2))) <$> distribution)
    (RegistrationBeaconReferenceGenericAgreement.stage_native setup
      (trusted setup wire route sign seed selectedScalar provider) seed (localScalar.getD selectedScalar)
      owner oneTime authenticated coherent (RegistrationNativeRelatedFamily.empty, (env, before)))
  simpa only [Functor.map_map, Prod.map_def, id_eq] using native

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement.collect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement.agreement_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement.agreement_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement.agreement_source
