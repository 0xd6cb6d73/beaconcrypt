-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBirth
import BeaconcryptCore.Computational.RegistrationNativeOptionalFrame

/-! The candidate provider advances its genuine birth prefix only on an explicit successful creation. Arbitrary actual code with zero creation callbacks therefore retains that prefix, including decapsulation, public encapsulation, source failures and all World effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenBirth (borns)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeOptionalFrame (Keeps)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def IsCreate : (Spec n mlSource Unit).Domain → Prop
  | .inr (.inl .create) => True
  | _ => False

instance : DecidablePred (IsCreate (n := n) (mlSource := mlSource)) := fun query => by
  rcases query with other | (pool | key)
  · exact inferInstanceAs (Decidable False)
  · cases pool with
    | create => exact isTrue trivial
    | decapsulate index ciphertext => exact isFalse (by intro impossible; cases impossible)
    | reveal index => exact isFalse (by intro impossible; cases impossible)
  · exact inferInstanceAs (Decidable False)

private theorem pool_counter (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (query : PqxdhLiveKemBirth.Query) (ordinary : query ≠ .create)
    (before after : PqxdhDynamicKemRouter.State KemSK) (reply : Option ((PqxdhLiveKemBirth.PoolSpec KemSK).Range query))
    (supported : (reply, after) ∈ support (((PqxdhDynamicKemRouter.source baseImpl kem selected pairs query).run).run before)) :
    after.created = before.created := by
  cases query with
  | create => exact False.elim (ordinary rfl)
  | decapsulate index ciphertext =>
      cases found : (pairs.take before.created)[index]? with
      | none =>
          simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found, pure_bind,
            mem_support_pure_iff, Prod.mk.injEq] at supported
          obtain ⟨rfl, rfl⟩ := supported
          rfl
      | some pair =>
          simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found, bind_pure_comp, support_map] at supported
          obtain ⟨value, _called, returned⟩ := supported
          have stateEq := congrArg Prod.snd returned
          cases stateEq
          rfl
  | reveal index =>
      cases found : (pairs.take before.created)[index]? with
      | none =>
          simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found,
            mem_support_pure_iff, Prod.mk.injEq] at supported
          obtain ⟨rfl, rfl⟩ := supported
          rfl
      | some pair =>
          by_cases chosen : index = selected
          · simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found] at supported
            simp only [chosen, ite_true,
              mem_support_pure_iff, Prod.mk.injEq] at supported
            obtain ⟨rfl, rfl⟩ := supported
            rfl
          · simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found] at supported
            simp only [chosen, ite_false,
              mem_support_pure_iff, Prod.mk.injEq] at supported
            obtain ⟨rfl, rfl⟩ := supported
            rfl

private theorem candidate_counter (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : PqxdhLiveKemBirth.Query) (ordinary : query ≠ .create)
    (before after : PqxdhDynamicKemRouter.State KemSK) (reply : Option ((PqxdhLiveKemBirth.PoolSpec KemSK).Range query))
    (supported : (reply, after) ∈ support (((RegistrationNativeKemCandidatePool.source baseImpl kem selected pairs challenge candidate query).run).run before)) :
    after.created = before.created := by
  cases query with
  | create => exact False.elim (ordinary rfl)
  | decapsulate index ciphertext =>
      cases found : (pairs.take before.created)[index]? with
      | none =>
          simp only [RegistrationNativeKemCandidatePool.source, OptionT.run_mk, StateT.run, found, pure_bind,
            mem_support_pure_iff, Prod.mk.injEq] at supported
          obtain ⟨rfl, rfl⟩ := supported
          rfl
      | some pair =>
          by_cases chosen : index = selected ∧ ciphertext = challenge
          · simp only [RegistrationNativeKemCandidatePool.source, OptionT.run_mk, StateT.run, found] at supported
            simp only [chosen, pure_bind] at supported
            obtain ⟨rfl, rfl⟩ := supported
            rfl
          · simp only [RegistrationNativeKemCandidatePool.source, OptionT.run_mk, StateT.run, found, chosen,
              ite_false, bind_pure_comp, support_map] at supported
            obtain ⟨value, _called, returned⟩ := supported
            have stateEq := congrArg Prod.snd returned
            cases stateEq
            rfl
  | reveal index => exact pool_counter baseImpl kem selected pairs (.reveal index) (by intro impossible; cases impossible) before after reply supported

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Every actual noncreation callback retains the current genuine birth prefix under the complete candidate provider. -/
theorem query_counter (query : (Spec n mlSource KemSK).Domain) (ordinary : ¬ IsCreate query)
    (before after : State n mlSource KemSK) (reply : (Spec n mlSource KemSK).Range query)
    (supported : (some reply, after) ∈ support (((provider query).run).run before)) : borns after = borns before := by
  rcases query with other | (pool | key)
  · rw [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchFacts.ambient_run, support_map] at supported
    obtain ⟨result, _called, returned⟩ := supported
    cases returned
    rfl
  · have different : pool ≠ .create := by intro same; subst pool; exact ordinary trivial
    cases phase : before.2 with
    | none =>
        simp only [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.source, phase,
          RegistrationNativeKemSwitchSource.carry, RegistrationNativeKemGame.stopped, RegistrationNativeKemGame.combine,
          OptionT.run_mk, StateT.run, Functor.map_map, support_map] at supported
        obtain ⟨result, called, returned⟩ := supported
        have stateEq := congrArg Prod.snd returned
        change ((before.1.1, result.2), none) = after at stateEq
        rw [← stateEq]
        exact pool_counter setup.baseImpl setup.kem selected pairs pool different _ _ _ called
    | some label =>
        simp only [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.source, phase,
          RegistrationNativeKemSwitchSource.post, RegistrationNativeKemSwitchSource.carry,
          RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
          OptionT.run_mk, StateT.run, Functor.map_map, support_map] at supported
        obtain ⟨result, called, returned⟩ := supported
        have stateEq := congrArg Prod.snd returned
        change ((before.1.1, result.2), some label) = after at stateEq
        rw [← stateEq]
        exact candidate_counter setup.baseImpl setup.kem selected pairs label.1 label.2 pool different _ _ _ called
  · cases phase : before.2 with
    | some label =>
        simp only [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.source, phase,
          RegistrationNativeKemSwitchSource.post, RegistrationNativeKemSwitchSource.carry,
          RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
          OptionT.run_mk, StateT.run, Functor.map_map, support_map] at supported
        obtain ⟨result, _called, returned⟩ := supported
        cases returned
        rfl
    | none =>
        simp only [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.source, phase,
          OptionT.run_mk, StateT.run, mem_support_bind_iff] at supported
        obtain ⟨pair, _generated, uniform, _sampled, called⟩ := supported
        by_cases matching : key = publicKey
        · simp only [matching, ite_true, pure_bind, mem_support_pure_iff, Prod.mk.injEq] at called
          obtain ⟨_replyEq, stateEq⟩ := called
          rw [stateEq]
          rfl
        · simp only [matching, ite_false, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at called
          obtain ⟨value, _encapsulated, _replyEq, stateEq⟩ := called
          rw [stateEq]
          rfl

/-- Arbitrary actual source work with no creation callback preserves the current genuine birth prefix, independently of cryptographic replies. -/
theorem no_create_keeps (work : OracleComp (Spec n mlSource KemSK) Value) (bounded : work.IsQueryBoundP IsCreate 0) :
    Keeps borns provider work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact RegistrationNativeOptionalFrame.pure_keeps borns provider value
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, following⟩ := bounded
      apply RegistrationNativeOptionalFrame.bind_keeps borns provider _ _ _
        (fun reply => ih reply (by simpa using following reply))
      intro before after reply supported
      rw [simulateQ_spec_query] at supported
      exact query_counter setup checks wire route representation created credential selected pairs publicKey real
        query (allowed.resolve_right (by omega)) before after reply supported

end BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame.query_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame.query_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame.no_create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame.no_create_keeps
