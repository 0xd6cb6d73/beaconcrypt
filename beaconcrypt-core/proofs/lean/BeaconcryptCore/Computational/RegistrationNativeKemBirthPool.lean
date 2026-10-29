-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemInterface

/-! The actual indexed source can only append a genuinely generated pair. Every old handle remains bound to its exact private pair across all callbacks, even when public-key bytes alias. These support facts include rejected decapsulation and ordinary local effects. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBirthPool
open PqxdhKemIndCca
open PqxdhLiveKemBirth (Pool)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

def Generated (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (pool : Pool KemSK) : Prop :=
  ∀ pair ∈ pool.keys, pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen)

def KeyStep (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (before after : Pool KemSK) : Prop :=
  after.keys = before.keys ∨
    ∃ pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen),
      after.keys = before.keys ++ [pair]

private theorem pool_step (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (query : PqxdhLiveKemBirth.Query)
    (before : Pool KemSK) (reply : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query) (after : Pool KemSK)
    (supported : (reply, after) ∈ support ((PqxdhLiveKemBirth.poolImpl baseImpl kem query).run before)) :
    KeyStep baseImpl kem before after := by
  cases query with
  | create =>
      simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, support_map] at supported
      obtain ⟨pair, generated, returned⟩ := supported
      cases returned
      exact Or.inr ⟨pair, generated, rfl⟩
  | decapsulate handle ciphertext =>
      cases found : before.keys[handle]? with
      | none =>
          simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, found, pure_bind,
            support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact Or.inl rfl
      | some pair =>
          simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, found, mem_support_bind_iff] at supported
          obtain ⟨answer, _, returned⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at returned
          cases returned
          exact Or.inl rfl
  | reveal handle =>
      simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl rfl

/-- Every actual native source callback preserves the pool or appends one actual key-generation result. -/
theorem source_step (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (query : (RegistrationNativeKemInterface.Spec ambient KemSK).Domain)
    (before after : Auxiliary × Pool KemSK)
    (reply : (RegistrationNativeKemInterface.Spec ambient KemSK).Range query)
    (supported : (reply, after) ∈ support
      ((RegistrationNativeKemInterface.source baseImpl kem ambient other query).run before)) :
    KeyStep baseImpl kem before.2 after.2 := by
  rcases query with query | (query | key)
  · simp only [RegistrationNativeKemInterface.source, StateT.run, support_map] at supported
    obtain ⟨result, _, returned⟩ := supported
    cases returned
    exact Or.inl rfl
  · simp only [RegistrationNativeKemInterface.source, StateT.run, support_map] at supported
    obtain ⟨result, reached, returned⟩ := supported
    cases returned
    exact pool_step baseImpl kem query before.2 result.1 result.2 reached
  · simp only [RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨result, _, returned⟩ := supported
    cases returned
    exact Or.inl rfl

/-- Actual source steps retain the generator receipt of every private key, including all earlier owners. -/
theorem generated_step (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (before after : Pool KemSK)
    (prior : Generated baseImpl kem before) (step : KeyStep baseImpl kem before after) :
    Generated baseImpl kem after := by
  rcases step with same | ⟨new, generated, appended⟩
  · simpa only [Generated, same] using prior
  · intro pair member
    rw [appended, List.mem_append, List.mem_singleton] at member
    rcases member with earlier | rfl
    · exact prior pair earlier
    · exact generated

/-- Private handles resolve to the same actual pair after any source callback; no injectivity of public keys is needed. -/
theorem lookup_step (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (before after : Pool KemSK)
    (step : KeyStep baseImpl kem before after) (handle : Nat) (pair : MlKem768PublicKey × KemSK)
    (found : before.keys[handle]? = some pair) : after.keys[handle]? = some pair := by
  rcases step with same | ⟨_, _, appended⟩
  · simpa only [same] using found
  · rw [appended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found

end BeaconcryptCore.Computational.RegistrationNativeKemBirthPool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthPool.source_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthPool.source_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthPool.generated_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthPool.generated_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthPool.lookup_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthPool.lookup_step
