-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly

/-! Genuine constructor alignment uses the actual early provider's creation index and unchanged key list on every other operation. These supported-transition facts retain opaque private handles rather than assuming an equality to a roster position. They apply before and after the selected getter, including pre-getter selected decapsulation and nonmatching public encapsulation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys
open PqxdhKemIndCca
open PqxdhLiveKemBirth (Query)
open RegistrationNativeSecretWordKemInterface (Routed WordPoolSpec)
open RegistrationNativeSecretWordKemProvider (State ordinary pool)
open RegistrationNativeSecretWordKemEarly (early)
open RegistrationNativeSecretWordKemPool (Pool record created)
variable {ι KemSK : Type} {base : OracleSpec ι}

def Creates : (Routed KemSK).Domain → Prop
  | .inr (.inl .create) => True
  | _ => False

private theorem pool_noncreate (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext)
    (query : Query) (quiet : query ≠ .create) (before : Pool KemSK)
    (result : (WordPoolSpec KemSK).Range query × Pool KemSK)
    (supported : result ∈ support ((pool baseImpl kem selected pairs (some challenge) query).run before)) :
    result.2.keys = before.keys := by
  cases query with
  | create => exact (quiet rfl).elim
  | reveal handle =>
      simp only [pool, StateT.run, mem_support_pure_iff] at supported
      cases supported
      rfl
  | decapsulate handle ciphertext =>
      cases found : before.keys[handle]? <;>
        simp only [pool, StateT.run, found, bind_pure_comp] at supported
      all_goals try split at supported
      all_goals simp only [support_map] at supported
      all_goals obtain ⟨answer, _sampled, returned⟩ := supported
      all_goals cases returned
      all_goals rfl

private theorem ordinary_noncreate (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext)
    (query : (Routed KemSK).Domain) (quiet : ¬Creates (KemSK := KemSK) query) (before : State KemSK)
    (result : (Routed KemSK).Range query × State KemSK)
    (supported : result ∈ support ((ordinary baseImpl kem selected pairs (some challenge) query).run before)) :
    result.2.1.keys = before.1.keys := by
  rcases query with (query | key) | query | key
  all_goals simp only [ordinary, StateT.run, support_map] at supported
  all_goals obtain ⟨answer, sampled, returned⟩ := supported
  all_goals cases returned
  all_goals first
    | rfl
    | (apply pool_noncreate baseImpl kem selected pairs challenge query _ before.1 answer sampled
       intro same
       subst query
       exact quiet trivial)

/-- Every actual noncreation transition preserves the exact private generated-key list, including a first selected getter and all optional decapsulation failures. -/
theorem noncreate_keys (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (query : (Routed KemSK).Domain) (quiet : ¬Creates (KemSK := KemSK) query) (before : State KemSK)
    (result : (Routed KemSK).Range query × State KemSK)
    (supported : result ∈ support ((early baseImpl kem selected pairs publicKey challenge query).run before)) :
    result.2.1.keys = before.1.keys := by
  rcases query with (query | key) | query | key
  all_goals try (exact ordinary_noncreate baseImpl kem selected pairs challenge _ quiet before result supported)
  case inr.inr =>
    cases phase : before.2 with
    | some value =>
        apply ordinary_noncreate baseImpl kem selected pairs challenge (.inr (.inr key)) quiet before result
        simpa only [early, StateT.run, phase] using supported
    | none =>
        simp only [early, StateT.run, phase, mem_support_bind_iff] at supported
        obtain ⟨_dummy, _drawn, continued⟩ := supported
        by_cases matching : key = publicKey
        · simp only [matching, ite_true, pure_bind, mem_support_pure_iff] at continued
          cases continued
          rfl
        · simp only [matching, ite_false, mem_support_bind_iff] at continued
          obtain ⟨reply, _encapsulated, returned⟩ := continued
          simp only [mem_support_pure_iff] at returned
          cases returned
          rfl

/-- Actual reserved creation returns its real next private index and public key, appending that exact pair once while preserving the getter marker. -/
theorem create_reserved (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (before : State KemSK) (pair : MlKem768PublicKey × KemSK)
    (available : pairs[before.1.keys.length]? = some pair) :
    (early baseImpl kem selected pairs publicKey challenge (.inr (.inl .create))).run before =
      pure ((created before.1 pair).1, ((created before.1 pair).2, before.2)) := by
  cases before with
  | mk before marker =>
      cases marker <;> simp only [early, ordinary, pool, StateT.run, available, map_pure]

private theorem ordinary_phase (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext)
    (query : (Routed KemSK).Domain) (before : State KemSK) (result : (Routed KemSK).Range query × State KemSK)
    (supported : result ∈ support ((ordinary baseImpl kem selected pairs (some challenge) query).run before)) :
    result.2.2 = before.2 := by
  rcases query with (query | key) | query | key
  all_goals simp only [ordinary, StateT.run, support_map] at supported
  all_goals obtain ⟨answer, _sampled, returned⟩ := supported
  all_goals cases returned
  all_goals rfl

/-- Every actual non-exposed request preserves the getter marker, including creation and optional selected-handle decapsulation. -/
theorem nonexposed_phase (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (query : (Routed KemSK).Domain)
    (quiet : ¬RegistrationNativeKemRouting.IsExposed (ambient := RegistrationNativeKemInterface.OtherSpec) (KemSK := KemSK) query)
    (before : State KemSK) (result : (Routed KemSK).Range query × State KemSK)
    (supported : result ∈ support ((early baseImpl kem selected pairs publicKey challenge query).run before)) :
    result.2.2 = before.2 := by
  rcases query with left | query | key
  · exact ordinary_phase baseImpl kem selected pairs challenge (.inl left) before result supported
  · exact ordinary_phase baseImpl kem selected pairs challenge (.inr (.inl query)) before result supported
  · exact (quiet trivial).elim

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys.noncreate_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys.noncreate_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys.create_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys.create_reserved

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys.nonexposed_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys.nonexposed_phase
