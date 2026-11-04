-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecipientFailure
import BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows

/-! The actual Beacon collector's KEM coordinate is fixed by its reached private row and received ciphertext under explicit functional decapsulation. This is determinism, not perfect recipient correctness. It lets a same-run Server encapsulation witness charge a concrete finite-row marker without selecting an arbitrary primitive support witness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeKemCountedRecipientSample (Draw)
variable {n count : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (functional : FunctionalDecapsulation setup.kem)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
variable (authenticated : registration.AuthenticatedResponse)
variable (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
variable (before after : Local n KemSK source)
variable (supported : (some input, after) ∈ support ((simulateQ
  (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query))
  (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
    (PqxdhBeaconPhase2Preparation.collect () false true () []))).run before))
variable (pair : RegistrationNativeKemCountedReservedRows.Pair KemSK)
variable (found : before.2.2.pool.keys[owner.kemHandle]? = some pair)

include supported found in
/-- Every supported actual collector result has the same recipient coordinate for that concrete received ciphertext and private row. -/
theorem collected : functional.result pair.2 (PqxdhPhase2InputBytes.ciphertext authenticated.packet.public.kem_cipher_text) =
    some (PqxdhPhase2InputBytes.word input.finishInputs.shared_secrets.kem_shared_secret) := by
  obtain ⟨_converted, actualPair, _public, _private, actualRow, decapsulated, _rest⟩ :=
    RegistrationNativeBeaconCollectedOperands.collect setup checks representation created owner oneTime authenticated input before after supported
  have same : actualPair = pair := Option.some.inj (actualRow.symm.trans found)
  subst actualPair
  rw [functional.exact, simulateQ_pure] at decapsulated
  simp only [support_pure, Set.mem_singleton_iff] at decapsulated
  exact decapsulated.symm

include supported found in
/-- A mismatch with one actual same-ciphertext encapsulation reply is an actual finite-row primitive error, including aliased public keys. -/
theorem mismatch (rows : Fin count → Draw KemSK)
    (covered : RegistrationNativeKemCountedReservedRows.Covered (List.ofFn rows) before.2.2.pool)
    (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret)
    (ciphertext : PqxdhPhase2InputBytes.ciphertext authenticated.packet.public.kem_cipher_text = encapsulated.1)
    (different : PqxdhPhase2InputBytes.word input.finishInputs.shared_secrets.kem_shared_secret ≠ encapsulated.2)
    (cost : Nat) : RegistrationNativeKemCountedRecipientFamily.AnyBad setup functional rows
      (.inr (.inr pair.1)) (encapsulated, cost) := by
  have recovered := collected setup checks functional representation created owner oneTime authenticated input before after supported pair found
  rw [ciphertext] at recovered
  have member := covered pair (List.mem_of_getElem? found)
  obtain ⟨drawn, drawnMember, samePair⟩ := List.mem_map.mp member
  obtain ⟨target, named⟩ := List.mem_ofFn.mp drawnMember
  have selected : (rows target).1 = pair := (congrArg Prod.fst named).trans samePair
  refine ⟨target, ?_⟩
  simp only [RegistrationNativeKemCountedRecipient.Bad, selected, true_and]
  rw [recovered]
  exact fun same => different (Option.some.inj same)
include supported found in
/-- The source Root's actual KEM reply coordinate agrees with the Beacon coordinate unless that very encapsulation reply triggers the finite-family marker. -/
theorem coordinate_or_marker (rows : Fin count → Draw KemSK)
    (covered : RegistrationNativeKemCountedReservedRows.Covered (List.ofFn rows) before.2.2.pool)
    (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret)
    (ciphertext : PqxdhPhase2InputBytes.ciphertext authenticated.packet.public.kem_cipher_text = encapsulated.1)
    (serverKem : Std.Array U8 32#usize) (actualKem : serverKem = PqxdhRootTableInitialization.rootArray encapsulated.2)
    (cost : Nat) : serverKem = input.finishInputs.shared_secrets.kem_shared_secret ∨
      RegistrationNativeKemCountedRecipientFamily.AnyBad setup functional rows (.inr (.inr pair.1)) (encapsulated, cost) := by
  by_cases same : PqxdhPhase2InputBytes.word input.finishInputs.shared_secrets.kem_shared_secret = encapsulated.2
  · have lifted := congrArg PqxdhRootTableInitialization.rootArray same
    rw [PqxdhPhase2InputBytes.word_roundtrip] at lifted
    exact Or.inl (actualKem.trans lifted.symm)
  · exact Or.inr (mismatch setup checks functional representation created owner oneTime authenticated input before after supported pair found
      rows covered encapsulated ciphertext same cost)

end BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional.collected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional.collected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional.mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional.mismatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional.coordinate_or_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecipientFunctional.coordinate_or_marker
