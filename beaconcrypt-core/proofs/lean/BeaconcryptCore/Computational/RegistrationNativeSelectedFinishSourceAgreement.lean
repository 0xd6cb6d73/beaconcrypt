-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation

/-! The actual selected-owner collector and literal preparation reconstruct the native arbitrary-pin root phase on one reached World and indexed pool. The source memo is retained in the execution and projected only in this comparison; successful preparation separately supplies the fresh memo receipt used by completion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev Frame (n : Nat) (KemSK : Type) := PqxdhRecordLiftWorld.State n × PqxdhLiveKemBirth.Pool KemSK × List RegistrationSigningShared.Receipt

def frame (before : Private n KemSK) : Frame n KemSK := (before.world, before.pool, before.extra.2)

noncomputable def trusted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT (Private n KemSK) ProbComp) :=
  implementation setup wire route sign seed scalar ∘ₛ RegistrationBeaconReferenceCompiler.trustedLift

/-- The actual scalar-free collection has exactly the same ordinary interpreter and complete reached private state. -/
theorem collect_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : EnvState Auxiliary) (before : Private n KemSK) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (implementation setup wire route sign seed scalar)
        ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env)).run before =
      (RegistrationBeaconReferenceGenericStage.lower setup (trusted setup wire route sign seed scalar)
        (RegistrationBeaconReferenceCompiler.trustedCollect setup owner oneTime authenticated)).run (env, before) := by
  rw [← RegistrationBeaconReferenceCallbacks.collect_lift, ← QueryImpl.simulateQ_compose]
  rfl

/-- Literal preparation reconstructs the exact native root stage, without an owner-pin or ML-key-membership premise. -/
theorem agreement_stage (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : EnvState Auxiliary) (before : Private n KemSK) :
    (fun result => (restored result.2.extra.1 authenticated result.1.1, (result.1.2, frame result.2))) <$>
      (simulateQ (implementation setup wire route sign seed scalar)
        ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env)).run before =
      (fun result => (result.1, (result.2.2.1, frame result.2.2.2))) <$>
        (RegistrationBeaconReferenceGenericAgreement.stage setup (trusted setup wire route sign seed scalar) owner oneTime
          (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh seed scalar)
          authenticated).run (RegistrationNativeRelatedFamily.empty, (env, before)) := by
  rw [RegistrationBeaconReferenceGenericAgreement.stage_run]
  simp only [RegistrationBeaconReferenceCompiler.agreement, StateT.run_bind, simulateQ_bind,
    StateT.run_bind, map_bind]
  have collected := collect_source setup wire route sign seed scalar owner oneTime authenticated env before
  rw [← collected, bind_map_left]
  apply bind_congr
  rintro ⟨⟨pending, afterEnv⟩, after⟩
  cases pending with
  | none =>
      simp only [StateT.run_pure, simulateQ_pure, map_pure, restored,
        RegistrationBeaconReferenceRoot.restored, frame]
  | some pending =>
      have actual := RegistrationNativeOrdinaryFinishSourceSelectedPreparation.client_source setup wire route sign seed scalar authenticated pending after
      have root := RegistrationNativeSourceRoot.program_value setup.source setup.hmac setup.joint setup.dh seed scalar
        (RegistrationNativeBeaconRootSource.client authenticated pending) RegistrationNativeRelatedFamily.empty
      rw [← root] at actual
      have mapped := congrArg (fun distribution => (fun result => (result.1, (afterEnv, result.2))) <$> distribution) actual
      simpa only [StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map,
        Functor.map_map, Prod.map_def, id_eq, frame] using mapped

/-- The complete literal selected-owner preparation is the actual native agreement controller under the same concrete ordinary interpreter. -/
theorem agreement_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (env : EnvState Auxiliary) (before : Private n KemSK) :
    (fun result => (restored result.2.extra.1 authenticated result.1.1, (result.1.2, frame result.2))) <$>
      (simulateQ (implementation setup wire route sign seed scalar)
        ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env)).run before =
      (fun result => (result.1, (result.2.1, frame result.2.2))) <$>
        (simulateQ (RegistrationBeaconReferenceGenericStage.native setup (trusted setup wire route sign seed scalar) scalar owner oneTime)
          (RegistrationAgreementExecutor.beacon authenticated)).run (env, before) := by
  rw [agreement_stage]
  have native := congrArg (fun distribution => (fun result => (result.1, (result.2.1, frame result.2.2))) <$> distribution)
    (RegistrationBeaconReferenceGenericAgreement.stage_native setup (trusted setup wire route sign seed scalar) seed scalar owner oneTime
      authenticated coherent (RegistrationNativeRelatedFamily.empty, (env, before)))
  simpa only [Functor.map_map, Prod.map_def, id_eq] using native

end BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement.collect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement.agreement_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement.agreement_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement.agreement_source
