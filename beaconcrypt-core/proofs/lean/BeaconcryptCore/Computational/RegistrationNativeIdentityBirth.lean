-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks

/-! Successful public identity credentials arise from the actual source sampler and its appended private seed. These receipts retain generated indices even when two public identities have equal bytes. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBirth
open PqxdhJointIdentity
open PqxdhDynamicIdentityPool
open RegistrationNativeIdentityInterface
variable {Index Auxiliary : Type} {ambient : OracleSpec Index}

/-- Source creation itself supplies the generated seed/public-key relation; no honesty or constructor-injectivity premise is required. -/
theorem generated (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives)
    (before after : State Auxiliary) (credential : Credential)
    (supported : (some credential, after) ∈ support
      ((simulateQ (source ambient ordinary primitives) (create ambient)).run before)) :
    ∃ seed ∈ support sampleSeed,
      credential.handle = before.2.seeds.length ∧
      credential.publicIdentity = primitives.publicKeys seed ∧
      after.1 = before.1 ∧ after.2.seeds = before.2.seeds ++ [seed] := by
  rw [create_source] at supported
  obtain ⟨seed, drawn, equal⟩ := OracleComp.mem_support_map_peel _ _ supported
  cases equal
  exact ⟨seed, drawn, rfl, rfl, rfl, rfl⟩

/-- Every successful credential identifies its exact new private source entry, with the same correlated public identity. -/
theorem owned (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives)
    (before after : State Auxiliary) (credential : Credential)
    (supported : (some credential, after) ∈ support
      ((simulateQ (source ambient ordinary primitives) (create ambient)).run before)) :
    ∃ seed ∈ support sampleSeed,
      RegistrationNativeIdentityCallbacks.Owns primitives after.2 credential seed := by
  obtain ⟨seed, drawn, handle, publicKey, _auxiliary, appended⟩ := generated ordinary primitives before after credential supported
  refine ⟨seed, drawn, ?_, publicKey⟩
  rw [appended, handle]
  simp only [List.getElem?_append, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero]

end BeaconcryptCore.Computational.RegistrationNativeIdentityBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBirth.generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBirth.generated
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBirth.owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBirth.owned
