-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation

/-! The actual native Beacon collector exposes its original table-key KEM computation and its four literal source DH replies. All classical callbacks preserve private rows, and no peer-root equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCollectedOperands
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeBeaconDhReplies
open RegistrationAgreementExecutor (Spec)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
local notation "implementation" => fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query)

private theorem pure_called (query : Spec.Domain) (answer returned : Spec.Range query)
    (primitive : RegistrationNativeBeaconFrontend.agreementCore (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup owner oneTime query = pure answer)
    (before after : Local n KemSK source)
    (supported : (returned, after) ∈ support ((implementation query).run before)) :
    answer = returned ∧ after.2.2 = before.2.2 := by
  rw [pure_step setup checks representation created owner oneTime query answer primitive before] at supported
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  exact ⟨supported.1.symm, congrArg (fun value => value.2.2) supported.2⟩

/-- The original collector retains the private KEM row and every ordered native source-DH value. -/
theorem collect (authenticated : registration.AuthenticatedResponse)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
    (before after : Local n KemSK source)
    (supported : (some input, after) ∈ support ((simulateQ implementation
      (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
        (PqxdhBeaconPhase2Preparation.collect () false true () []))).run before)) :
    ∃ converted pair,
      RegistrationPublicConversion.convert setup.source.crypto authenticated.packet.public.identity_key = .Some converted ∧
      RegistrationServerRoleBackend.selectedConversion setup.source.crypto (setup.secretOfSeed owner.identitySeed) = true ∧
      before.2.2.pool.keys[owner.kemHandle]? = some pair ∧
      some (PqxdhPhase2InputBytes.word input.finishInputs.shared_secrets.kem_shared_secret) ∈ support
        (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
          (setup.kem.decaps pair.2 (PqxdhPhase2InputBytes.ciphertext authenticated.packet.public.kem_cipher_text))) ∧
      reply setup owner oneTime ⟨.BeaconPrekey, converted⟩ = .Some input.finishInputs.shared_secrets.dh1 ∧
      reply setup owner oneTime ⟨.LocalIdentity, authenticated.packet.public.ephemeral_key⟩ = .Some input.finishInputs.shared_secrets.dh2 ∧
      reply setup owner oneTime ⟨.BeaconPrekey, authenticated.packet.public.ephemeral_key⟩ = .Some input.finishInputs.shared_secrets.dh3 ∧
      reply setup owner oneTime ⟨.BeaconOneTime, authenticated.packet.public.ephemeral_key⟩ = .Some input.finishInputs.shared_secrets.dh4 ∧
      after.2.2.pool.keys = before.2.2.pool.keys := by
  obtain ⟨converted, convertedState, identityState, kemState, firstState, secondState, thirdState,
      convertedCalled, identityCalled, kemCalled, firstCalled, secondCalled, thirdCalled, fourthCalled⟩ :=
    RegistrationNativeBeaconCollectorCuts.collect implementation authenticated input before after supported
  obtain ⟨convertedEq, convertedNative⟩ := pure_called setup checks representation created owner oneTime (.convertPublic authenticated.packet.public.identity_key) _ _
    (primitive_public setup owner oneTime _) _ _ convertedCalled
  obtain ⟨identityEq, identityNative⟩ := pure_called setup checks representation created owner oneTime (.convertSecret .LocalIdentity) _ _
    (primitive_identity setup owner oneTime) _ _ identityCalled
  obtain ⟨pair, row, decapsulated, keys⟩ := RegistrationNativeBeaconDecapsulation.agreement
    setup checks representation created owner oneTime _ _ _ _ kemCalled
  obtain ⟨firstEq, firstNative⟩ := pure_called setup checks representation created owner oneTime (.dh ⟨.BeaconPrekey, converted⟩) _ _
    (primitive_dh setup owner oneTime _) _ _ firstCalled
  obtain ⟨secondEq, secondNative⟩ := pure_called setup checks representation created owner oneTime (.dh ⟨.LocalIdentity, authenticated.packet.public.ephemeral_key⟩) _ _
    (primitive_dh setup owner oneTime _) _ _ secondCalled
  obtain ⟨thirdEq, thirdNative⟩ := pure_called setup checks representation created owner oneTime (.dh ⟨.BeaconPrekey, authenticated.packet.public.ephemeral_key⟩) _ _
    (primitive_dh setup owner oneTime _) _ _ thirdCalled
  obtain ⟨fourthEq, fourthNative⟩ := pure_called setup checks representation created owner oneTime (.dh ⟨.BeaconOneTime, authenticated.packet.public.ephemeral_key⟩) _ _
    (primitive_dh setup owner oneTime _) _ _ fourthCalled
  have identityBefore := identityNative.trans convertedNative
  refine ⟨converted, pair, convertedEq, identityEq, identityBefore ▸ row, decapsulated,
    firstEq, secondEq, thirdEq, fourthEq, ?_⟩
  exact (congrArg (fun state => state.pool.keys)
    (fourthNative.trans (thirdNative.trans (secondNative.trans firstNative)))).trans
      (keys.trans (congrArg (fun state => state.pool.keys) identityBefore))

end BeaconcryptCore.Computational.RegistrationNativeBeaconCollectedOperands

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCollectedOperands.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCollectedOperands.collect
