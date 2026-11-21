-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys

/-! The actual early provider creates one genuine indexed pair even beyond the private reservation. Its returned handle is the current private key-list length and its public key is the appended pair. This unconditional transition law supports the owner-roster alignment invariant separately from reservation-cap accounting. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth
open PqxdhKemIndCca
open RegistrationNativeSecretWordKemEarly (early)
open RegistrationNativeSecretWordKemProvider (State ordinary pool)
open RegistrationNativeSecretWordKemPool (created)
variable {ι KemSK : Type} {base : OracleSpec ι}

/-- Actual creation returns and appends the same genuine pair, including the ordinary-keygen fallback when the reservation has no next entry. -/
theorem create_step (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (before : State KemSK) (result : (Nat × MlKem768PublicKey) × State KemSK)
    (supported : result ∈ support ((early baseImpl kem selected pairs publicKey challenge (.inr (.inl .create))).run before)) :
    ∃ pair, result.1 = (before.1.keys.length, pair.1) ∧ result.2.1.keys = before.1.keys ++ [pair] ∧ result.2.2 = before.2 := by
  have normalized : (early baseImpl kem selected pairs publicKey challenge (.inr (.inl .create))).run before =
      (fun pair => ((created before.1 pair).1, ((created before.1 pair).2, before.2))) <$>
        (match pairs[before.1.keys.length]? with
        | none => simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen
        | some pair => pure pair) := by
    rcases before with ⟨before, marker⟩
    cases marker <;> cases available : pairs[before.keys.length]? <;>
      simp only [early, ordinary, pool, StateT.run, available, map_pure, Functor.map_map]
  rw [normalized, support_map] at supported
  obtain ⟨pair, _sampled, rfl⟩ := supported
  exact ⟨pair, rfl, rfl, rfl⟩

/-- Every actual creation grows the active private key list by exactly one and returns its old length. -/
theorem create_length (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (before : State KemSK) (result : (Nat × MlKem768PublicKey) × State KemSK)
    (supported : result ∈ support ((early baseImpl kem selected pairs publicKey challenge (.inr (.inl .create))).run before)) :
    result.1.1 = before.1.keys.length ∧ result.2.1.keys.length = before.1.keys.length + 1 := by
  obtain ⟨pair, reply, keys, _phase⟩ := create_step baseImpl kem selected pairs publicKey challenge before result supported
  rw [reply, keys, List.length_append]
  exact ⟨rfl, rfl⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth.create_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth.create_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth.create_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth.create_length
