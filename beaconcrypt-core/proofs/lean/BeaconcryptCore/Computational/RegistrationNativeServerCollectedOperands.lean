-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies

/-! Successful original Server collection retains one actual generated scalar and an actual encapsulation, with all four DH replies evaluated using that same scalar. These are source receipts, without a peer input or root equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerCollectedOperands
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeServerPrimitiveReplies
variable {ι KemSK : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : IdentitySeed)
local notation "Shared" => RawCtxSharedPrimitive.SharedState RegistrationServerRoleBackend.State
local notation "implementation" => RegistrationAgreementShared.implementation setup.source (RegistrationServerRoleBackend.native setup checks representation seed)

/-- The source collector uses its one freshly generated scalar through every later classical callback and its literal supplied KEM key through encapsulation. -/
theorem collect (verified : PqxdhServerRootPreparation.Verified registration.InitPacket)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32) (before after : Shared)
    (supported : (some input, after) ∈ support ((simulateQ implementation
      (simulateQ RegistrationAgreementRoot.callbacks (PqxdhServerRootPreparation.collectVerified verified))).run before)) :
    ∃ scalar ∈ support PqxdhJointGapDh.sampleScalar,
    ∃ pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.encaps (RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray verified.keys.pqKey)))),
      input.ephemeral.publicKey = rootArray (setup.dh.publicKey scalar) ∧
      input.ciphertext = PqxdhAcceptedRegistration.ciphertextArray pair.1 ∧ input.kem = rootArray pair.2 ∧
      RegistrationPublicConversion.convert setup.source.crypto (rootArray verified.identity) = .Some input.convertedIdentity ∧
      RegistrationServerRoleBackend.selectedConversion setup.source.crypto (setup.secretOfSeed seed) = true ∧
      RegistrationAgreementRoot.nativeOption ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer (rootArray verified.keys.prekey))).map rootArray) = .Some input.first ∧
      RegistrationAgreementRoot.nativeOption ((PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar (PqxdhPhase2GapDhSource.peer input.convertedIdentity)).map rootArray) = .Some input.second ∧
      RegistrationAgreementRoot.nativeOption ((PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar (PqxdhPhase2GapDhSource.peer (rootArray verified.keys.prekey))).map rootArray) = .Some input.third ∧
      RegistrationAgreementRoot.nativeOption ((PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar (PqxdhPhase2GapDhSource.peer (rootArray verified.keys.oneTime))).map rootArray) = .Some input.fourth ∧
      after.1.ephemeral = some scalar ∧ after.2 = before.2 := by
  obtain ⟨generatedState, kemState, convertedState, identityState, firstState, secondState, thirdState,
      generatedCalled, kemCalled, convertedCalled, identityCalled, firstCalled, secondCalled, thirdCalled, fourthCalled⟩ :=
    RegistrationNativeServerCollectorCuts.collect implementation verified input before after supported
  obtain ⟨scalar, sampled, publicKey, ephemeral, cacheEq⟩ := generate setup checks representation seed _ _ _ generatedCalled
  obtain ⟨pair, encapsulated, ciphertextEq, kemEq, stateEq⟩ := encapsulate setup checks representation seed _ _ _ _ _ kemCalled
  subst kemState
  rw [public_conversion] at convertedCalled
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at convertedCalled
  rcases convertedCalled with ⟨converted, stateEq⟩
  subst convertedState
  rw [private_conversion] at identityCalled
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at identityCalled
  rcases identityCalled with ⟨identity, stateEq⟩
  subst identityState
  rw [dh] at firstCalled
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at firstCalled
  rcases firstCalled with ⟨first, stateEq⟩
  subst firstState
  rw [dh] at secondCalled
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at secondCalled
  rcases secondCalled with ⟨second, stateEq⟩
  subst secondState
  rw [dh] at thirdCalled
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at thirdCalled
  rcases thirdCalled with ⟨third, stateEq⟩
  subst thirdState
  rw [dh] at fourthCalled
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at fourthCalled
  rcases fourthCalled with ⟨fourth, stateEq⟩
  subst after
  refine ⟨scalar, sampled, pair, encapsulated, publicKey, ciphertextEq, kemEq, converted.symm, identity.symm, ?_, ?_, ?_, ?_, ephemeral, cacheEq⟩
  · simpa only [dhReply] using first.symm
  · simpa only [dhReply, ephemeral, Option.bind_some] using second.symm
  · simpa only [dhReply, ephemeral, Option.bind_some] using third.symm
  · simpa only [dhReply, ephemeral, Option.bind_some] using fourth.symm

end BeaconcryptCore.Computational.RegistrationNativeServerCollectedOperands

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerCollectedOperands.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerCollectedOperands.collect
