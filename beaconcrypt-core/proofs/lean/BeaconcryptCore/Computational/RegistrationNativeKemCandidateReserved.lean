-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource
import BeaconcryptCore.Computational.RegistrationNativeKemPoolSource

/-! The candidate hybrid has a total reserved-pool interpreter. Only decapsulation at the actually created selected handle and exact challenge ciphertext substitutes the candidate. Missing handles, other ciphertexts, creation and all reply histories retain their literal native semantics. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemPoolSource (project IsReveal)
open RegistrationNativeKemReservation (IsCreate)
open RegistrationNativeKemGame (State)
open PqxdhKemIndCca (MlKemScheme MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def reserved (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (Spec ambient KemSK) (StateT (Auxiliary × PqxdhLiveKemBirth.Pool KemSK) ProbComp) := fun query before =>
  match query with
  | .inr (.inl (.decapsulate index ciphertext)) => do
      let reply ← match before.2.keys[index]? with
        | none => pure none
        | some pair =>
            if index = selected ∧ ciphertext = challenge then pure (some candidate)
            else simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)
      pure (reply, (before.1, PqxdhLiveKemBirth.record (.decapsulate index ciphertext) reply before.2))
  | query => (RegistrationNativeKemReservation.reserved baseImpl kem other pairs query).run before

/-- Affordable production callbacks project the actual stopped candidate source to the total native candidate-pool step, including the entire actual reply history. -/
theorem step_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (Spec ambient KemSK).Domain) (before : State Auxiliary KemSK) (noReveal : ¬IsReveal query)
    (room : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs challenge candidate query).run).run before) =
      (fun result => (some result.1, result.2)) <$>
        (reserved baseImpl kem other selected pairs challenge candidate query).run (project pairs before) := by
  rcases query with query | (query | key)
  · exact RegistrationNativeKemPoolSource.step_source baseImpl kem other selected pairs (.inl query) before noReveal room
  · cases query with
    | create => exact RegistrationNativeKemPoolSource.step_source baseImpl kem other selected pairs (.inr (.inl .create)) before noReveal room
    | reveal index => exact False.elim (noReveal trivial)
    | decapsulate index ciphertext =>
        cases found : (pairs.take before.2.created)[index]? <;>
          simp only [RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
            RegistrationNativeKemCandidatePool.source, OptionT.run_mk, StateT.run, reserved, project,
            PqxdhDynamicKemRouter.sourcePool, found, map_bind, map_pure, PqxdhDynamicKemRouter.record,
            PqxdhLiveKemBirth.record]
        · rfl
        · split <;> simp only [map_bind, map_pure] <;> rfl
  · exact RegistrationNativeKemPoolSource.step_source baseImpl kem other selected pairs (.inr (.inr key)) before noReveal room

/-- Candidate substitution changes no created-index allowance or exhaustion flag. -/
theorem step_capacity (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (Spec ambient KemSK).Domain) (before : State Auxiliary KemSK) (clear : before.2.exhausted = false)
    (room : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((Spec ambient KemSK).Range query) × State Auxiliary KemSK)
    (supported : result ∈ support (((RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs challenge candidate query).run).run before)) :
    result.2.2.exhausted = false ∧ result.2.2.created ≤ before.2.created + (if IsCreate query then 1 else 0) := by
  rcases query with query | (query | key)
  · exact RegistrationNativeKemPoolSource.step_capacity baseImpl kem other selected pairs (.inl query) before clear room result supported
  · cases query with
    | create => exact RegistrationNativeKemPoolSource.step_capacity baseImpl kem other selected pairs (.inr (.inl .create)) before clear room result supported
    | reveal index => exact RegistrationNativeKemPoolSource.step_capacity baseImpl kem other selected pairs (.inr (.inl (.reveal index))) before clear room result supported
    | decapsulate index ciphertext =>
        simp only [RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine, OptionT.run_mk,
          StateT.run, support_map] at supported
        obtain ⟨inner, actual, rfl⟩ := supported
        simp only [RegistrationNativeKemCandidatePool.source, OptionT.run_mk, bind_pure_comp] at actual
        have retained (reply : Option MlKemSharedSecret) :
            (PqxdhDynamicKemRouter.record (.decapsulate index ciphertext) reply before.2).exhausted = false ∧
              (PqxdhDynamicKemRouter.record (.decapsulate index ciphertext) reply before.2).created ≤
                before.2.created + (if IsCreate (ambient := ambient) (KemSK := KemSK) (.inr (.inl (.decapsulate index ciphertext))) then 1 else 0) := by
          simpa only [PqxdhDynamicKemRouter.record, IsCreate, ite_false, Nat.add_zero, le_refl, and_true] using clear
        repeat' split at actual
        all_goals simp only [support_map, Set.mem_image] at actual
        all_goals obtain ⟨reply, _called, rfl⟩ := actual
        all_goals exact retained reply
  · exact RegistrationNativeKemPoolSource.step_capacity baseImpl kem other selected pairs (.inr (.inr key)) before clear room result supported

/-- Affordable non-revealing candidate-source callbacks always return an actual native reply. -/
theorem step_answer (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (Spec ambient KemSK).Domain) (before : State Auxiliary KemSK) (noReveal : ¬IsReveal query)
    (room : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((Spec ambient KemSK).Range query) × State Auxiliary KemSK)
    (supported : result ∈ support (((RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs challenge candidate query).run).run before)) :
    result.1.isSome = true := by
  have mapped := Set.mem_image_of_mem (Prod.map id (project pairs)) supported
  rw [← support_map, step_source baseImpl kem other selected pairs challenge candidate query before noReveal room, support_map] at mapped
  obtain ⟨reply, _reached, same⟩ := mapped
  exact congrArg (fun value => value.1.isSome) same.symm

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved.step_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved.step_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved.step_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved.step_capacity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved.step_answer' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved.step_answer
