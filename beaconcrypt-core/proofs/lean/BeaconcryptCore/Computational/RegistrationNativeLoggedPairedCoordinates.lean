-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource
import BeaconcryptCore.Computational.RegistrationNativeCollectedDh
import BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional
import BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource

/-! Genuine native collectors and the Server's same-run logged encapsulation agree on the four DH coordinates and on the recipient coordinate unless that actual logged reply triggers the common finite-recipient marker. No perfect KEM correctness, reconstructed later root or arbitrary primitive support sample is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemCountedServerTrace (Log)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n count : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (packet : registration.InitPacket) (initAuth : registration.AuthenticatedInit)
variable (serverBefore serverAfter : RegistrationNativeKemServerState.State n source) (completed : agreement.ServerAgreement)
variable (log : Log KemSK)
variable (receipt : RegistrationNativeKemTracedServerSource.Receipt setup checks representation created packet initAuth serverBefore serverAfter completed log)
variable (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
variable (authenticated : registration.AuthenticatedResponse) (beaconInput : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
variable (before after : Local n KemSK source)
variable (beaconCollected : (some beaconInput, after) ∈ support
  ((simulateQ (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query))
    (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
      (PqxdhBeaconPhase2Preparation.collect () false true () []))).run before))
variable (rows : Fin count → RegistrationNativeKemCountedRecipientSample.Draw KemSK) (target : Fin count)
variable (row : before.2.2.pool.keys[owner.kemHandle]? = some (rows target).1)
variable (pqKey : receipt.nativeInput.collected.verified.keys.pqKey = (rows target).1.1)
variable (ciphertext : authenticated.packet.public.kem_cipher_text = receipt.nativeInput.collected.ciphertext)

include beaconCollected row pqKey ciphertext in
/-- Recipient-coordinate disagreement is a bad reply at this exact native Root's already logged encapsulation entry. -/
theorem kem_or_bad : receipt.nativeInput.collected.kem = beaconInput.finishInputs.shared_secrets.kem_shared_secret ∨
    RegistrationNativeKemCountedRecipientFamily.AnyBad setup functional rows
      (.inr (.inr receipt.nativeInput.collected.verified.keys.pqKey))
      ((PqxdhPhase2InputBytes.ciphertext receipt.nativeInput.collected.ciphertext,
        PqxdhPhase2InputBytes.word receipt.nativeInput.collected.kem), receipt.cost) := by
  by_cases same : receipt.nativeInput.collected.kem = beaconInput.finishInputs.shared_secrets.kem_shared_secret
  · exact Or.inl same
  · have recovered := RegistrationNativeBeaconRecipientFunctional.collected setup checks functional representation created owner oneTime
      authenticated beaconInput before after beaconCollected (rows target).1 row
    rw [ciphertext] at recovered
    refine Or.inr ⟨target, pqKey, ?_⟩
    change functional.result (rows target).1.2 (PqxdhPhase2InputBytes.ciphertext receipt.nativeInput.collected.ciphertext) ≠
      some (PqxdhPhase2InputBytes.word receipt.nativeInput.collected.kem)
    intro equal
    have wordEq := Option.some.inj (recovered.symm.trans equal)
    have arrayEq := congrArg PqxdhRootTableInitialization.rootArray wordEq
    rw [PqxdhPhase2InputBytes.word_roundtrip, PqxdhPhase2InputBytes.word_roundtrip] at arrayEq
    exact same arrayEq.symm

variable (identity : receipt.nativeInput.collected.verified.identity = (setup.joint.publicKeys owner.identitySeed).ed25519)
variable (prekey : receipt.nativeInput.collected.verified.keys.prekey = setup.dh.publicKey owner.prekeyScalar)
variable (oneTimeKey : receipt.nativeInput.collected.verified.keys.oneTime = setup.dh.publicKey oneTime)
variable (serverIdentity : authenticated.packet.public.identity_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys created.seed).ed25519)
variable (ephemeral : authenticated.packet.public.ephemeral_key = receipt.nativeInput.collected.ephemeral.publicKey)

include beaconCollected row pqKey ciphertext identity prekey oneTimeKey serverIdentity ephemeral in
/-- The actual four DH coordinates agree, and KEM disagreement is tied to the same logged native encapsulation reply. -/
theorem collected :
    receipt.nativeInput.collected.first = beaconInput.finishInputs.shared_secrets.dh1 ∧
    receipt.nativeInput.collected.second = beaconInput.finishInputs.shared_secrets.dh2 ∧
    receipt.nativeInput.collected.third = beaconInput.finishInputs.shared_secrets.dh3 ∧
    receipt.nativeInput.collected.fourth = beaconInput.finishInputs.shared_secrets.dh4 ∧
    (receipt.nativeInput.collected.kem = beaconInput.finishInputs.shared_secrets.kem_shared_secret ∨
      RegistrationNativeKemCountedRecipientFamily.AnyBad setup functional rows
        (.inr (.inr receipt.nativeInput.collected.verified.keys.pqKey))
        ((PqxdhPhase2InputBytes.ciphertext receipt.nativeInput.collected.ciphertext,
          PqxdhPhase2InputBytes.word receipt.nativeInput.collected.kem), receipt.cost)) := by
  have serverCollected : (some receipt.nativeInput.collected, receipt.nativeInput.atRoot) ∈ support
      ((simulateQ (RegistrationAgreementShared.implementation setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed))
        (simulateQ RegistrationAgreementRoot.callbacks
          (PqxdhServerRootPreparation.collectVerified receipt.nativeInput.collected.verified))).run
            (RegistrationWorldAgreement.project serverBefore.server.world)) := by
    rw [receipt.nativeInput.verified]
    exact receipt.nativeInput.supported
  obtain ⟨first, second, third, fourth⟩ := RegistrationNativeCollectedDh.collect setup checks representation created owner oneTime
    receipt.nativeInput.collected.verified receipt.nativeInput.collected _ _ serverCollected authenticated beaconInput before after beaconCollected
      identity prekey oneTimeKey serverIdentity ephemeral
  exact ⟨first, second, third, fourth, kem_or_bad setup checks functional representation created packet initAuth serverBefore serverAfter completed log
    receipt owner oneTime authenticated beaconInput before after beaconCollected rows target row pqKey ciphertext⟩


include beaconCollected row pqKey ciphertext in
/-- In the actual retained finite-recipient experiment, this source Root's KEM coordinate agrees unless that experiment's common sticky marker has fired. -/
theorem kem_or_marker (work : OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) Value)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK Value count)
    (supported : result ∈ support (RegistrationNativeKemRecipientLogSource.experiment setup functional work count))
    (sameLog : log = result.2.1.1.2) (sameRows : rows = result.1) :
    receipt.nativeInput.collected.kem = beaconInput.finishInputs.shared_secrets.kem_shared_secret ∨ result.2.2 = true := by
  rcases kem_or_bad setup checks functional representation created packet initAuth serverBefore serverAfter completed log receipt owner oneTime
    authenticated beaconInput before after beaconCollected rows target row pqKey ciphertext with equal | bad
  · exact Or.inl equal
  · apply Or.inr
    apply RegistrationNativeKemRecipientLogSource.sound setup functional work count result supported
      ⟨.inr (.inr receipt.nativeInput.collected.verified.keys.pqKey),
        ((PqxdhPhase2InputBytes.ciphertext receipt.nativeInput.collected.ciphertext,
          PqxdhPhase2InputBytes.word receipt.nativeInput.collected.kem), receipt.cost)⟩
    · rw [← sameLog]
      exact receipt.encapsulated
    · rw [← sameRows]
      exact bad

end BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates.kem_or_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates.kem_or_bad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates.collected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates.collected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates.kem_or_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates.kem_or_marker
