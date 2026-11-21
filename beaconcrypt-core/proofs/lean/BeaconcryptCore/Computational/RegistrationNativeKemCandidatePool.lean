-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSource

/-! The native uniform postphase has an explicit private indexed source. Exactly a created selected handle at the challenge ciphertext returns the candidate; every other request retains its actual indexed optional decapsulation. Birth, history and disclosure stopping are unchanged, including future reserved owners. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidatePool
open PqxdhKemIndCca PqxdhDynamicKemRouter
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhDynamicKemPost (evaluate)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK) (OptionT (StateT (State KemSK) ProbComp))
  | .decapsulate index ciphertext => OptionT.mk fun before => do
      let reply ← match (pairs.take before.created)[index]? with
        | none => pure none
        | some pair =>
            if index = selected ∧ ciphertext = challenge then pure (some candidate)
            else simulateQ (kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)
      pure (some reply, record (.decapsulate index ciphertext) reply before)
  | query => PqxdhDynamicKemRouter.source baseImpl kem selected pairs query

/-- The complete actual postchallenge indexed callback is precisely candidate substitution at the created selected handle, without a correctness assumption. -/
theorem post_step (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (key, secret)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : PqxdhLiveKemBirth.Query) (before : State KemSK) :
    evaluate baseImpl kem secret challenge
      (((PqxdhDynamicKemRouter.post kem selected (redact selected pairs) challenge candidate query).run).run before) =
      (((source baseImpl kem selected pairs challenge candidate query).run).run before) := by
  cases query with
  | create =>
      cases found : pairs[before.created]? <;>
        simp [PqxdhDynamicKemRouter.post, router, source, PqxdhDynamicKemRouter.source,
          redact, found, evaluate, StateT.run]
  | reveal index =>
      by_cases earlier : index < before.created
      · cases found : pairs[index]? with
        | none => simp [PqxdhDynamicKemRouter.post, router, source, PqxdhDynamicKemRouter.source,
            lookup, redact, earlier, found, evaluate, StateT.run]
        | some pair =>
            by_cases chosen : index = selected
            · subst index
              simp [PqxdhDynamicKemRouter.post, router, source, PqxdhDynamicKemRouter.source,
                lookup, redact, earlier, found, evaluate, StateT.run]
            · simp [PqxdhDynamicKemRouter.post, router, source, PqxdhDynamicKemRouter.source,
                lookup, redact, earlier, found, chosen, evaluate, StateT.run]
      · simp [PqxdhDynamicKemRouter.post, router, source, PqxdhDynamicKemRouter.source,
          lookup, earlier, evaluate, StateT.run]
  | decapsulate index ciphertext =>
      simp only [PqxdhDynamicKemRouter.post, router, source, OptionT.run_mk, StateT.run,
        bind_pure_comp, evaluate, simulateQ_map]
      by_cases earlier : index < before.created
      · cases found : pairs[index]? with
        | none => simp [postDecapsulation, lookup, redact, earlier, found]
        | some pair =>
            by_cases chosen : index = selected
            · subst index
              have equal : pair = (key, secret) := Option.some.inj (found.symm.trans present)
              subst pair
              by_cases same : ciphertext = challenge
              · subst ciphertext
                simp [postDecapsulation, lookup, redact, earlier, present]
              · simp [postDecapsulation, lookup, redact, earlier, present, same,
                  KEMScheme.IND_CCA_postChallengeImpl, QueryImpl.add]
            · simp only [postDecapsulation, lookup, ite_eq_left earlier, redact, found,
                Option.map_some, List.getElem?_take, chosen, false_and, ite_false]
              rw [show simulateQ (kemAmbientImpl baseImpl)
                (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge)
                  (PqxdhPrivateKemSource.ccaAmbient (kem.decaps pair.2 ciphertext))) = _ from
                    PqxdhDynamicKemPost.ambient baseImpl kem secret challenge (kem.decaps pair.2 ciphertext)]
      · simp [postDecapsulation, lookup, earlier]

end BeaconcryptCore.Computational.RegistrationNativeKemCandidatePool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidatePool.post_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidatePool.post_step
