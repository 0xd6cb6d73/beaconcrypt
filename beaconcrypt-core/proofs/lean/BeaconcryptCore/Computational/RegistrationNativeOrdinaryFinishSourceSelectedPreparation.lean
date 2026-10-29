-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation

/-! The selected case uses the same reached memo as ordinary materialized preparation, with the original message returned literally. All source World, indexed pool and chronological signing receipt coordinates remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}

/-- Literal preparation stores its optional source root under the exact reference it returns. -/
theorem prepare_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (before : Private n KemSK) :
    (implementation setup wire route sign seed scalar (.inl message)).run before =
      let root := RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message
      pure (root.map (fun _ => message),
        { before with extra := (Function.update before.extra.1 message root, before.extra.2) }) := rfl

/-- Reconstruction follows the fresh returned root and retains the entire actual World, pool and receipt frame. -/
theorem client_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) (before : Private n KemSK) :
    (fun result => (restored result.2.extra.1 authenticated result.1,
      (result.2.world, result.2.pool, result.2.extra.2))) <$>
      (simulateQ (implementation setup wire route sign seed scalar)
        (simulateQ RegistrationBeaconReferenceCompiler.prepare
          (RegistrationBeaconReferenceRoot.client authenticated pending))).run before =
      (fun result => (result, (before.world, before.pool, before.extra.2))) <$>
        simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
          (RegistrationNativeBeaconRootSource.client authenticated pending) := by
  simp only [RegistrationBeaconReferenceRoot.client, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare]
  rw [StateT.run_map, prepare_run]
  simp only [RegistrationNativeBeaconRootSource.client, RegistrationNativeBeaconRootSource.root,
    simulateQ_map, simulateQ_spec_query, RegistrationNativeSourceRoot.handler, map_pure, Functor.map_map]
  cases rootEq : RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar
      (RegistrationNativeRelatedRoot.pinnedBeaconMessage pending.collected) <;>
    simp only [Option.map_none, Option.map_some, restored, Function.update_self]
  all_goals rfl

/-- Every successful capability names the source root just stored, even if an older memo cell was different. -/
theorem client_prepared (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (before after : Private n KemSK) (ready : RegistrationBeaconReferenceRoot.Ready)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (implementation setup wire route sign seed scalar)
        (simulateQ RegistrationBeaconReferenceCompiler.prepare
          (RegistrationBeaconReferenceRoot.client authenticated pending))).run before)) :
    ∃ root, after.extra.1 ready.reference = some root := by
  simp only [RegistrationBeaconReferenceRoot.client, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare] at supported
  rw [StateT.run_map, prepare_run] at supported
  simp only [map_pure, mem_support_pure_iff] at supported
  cases rootEq : RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar
      (RegistrationNativeRelatedRoot.pinnedBeaconMessage pending.collected) with
  | none => simp only [rootEq, Option.map_none] at supported; cases supported
  | some root =>
      simp only [rootEq, Option.map_some] at supported
      cases supported
      exact ⟨root, Function.update_self _ _ _⟩

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation.prepare_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation.client_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation.client_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceSelectedPreparation.client_prepared
