-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemInterface

/-! Actual native generated-key requests and complete private reservation have the same whole continued distribution at a proved creation cap. All other native effects retain their actual state and order. Selecting the future honest creation is a full execution equality; it is not inferred from an accepted packet's public key. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReservation
open RegistrationNativeKemInterface (Spec source)
open PqxdhKemIndCca (MlKemScheme MlKem768PublicKey)
open PqxdhLiveKemReservation (Pair samplePairs)
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def reserved (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (Pair KemSK)) :
    QueryImpl (Spec ambient KemSK) (StateT (Auxiliary × PqxdhLiveKemBirth.Pool KemSK) ProbComp) := fun query before =>
  match query with
  | .inr (.inl .create) => match pairs[before.2.keys.length]? with
      | none => (source baseImpl kem ambient other (.inr (.inl .create))).run before
      | some pair => pure ((PqxdhLiveKemBirth.created before.2 pair).1,
          (before.1, (PqxdhLiveKemBirth.created before.2 pair).2))
  | query => (source baseImpl kem ambient other query).run before

def IsCreate : (Spec ambient KemSK).Domain → Prop
  | .inr (.inl .create) => True
  | _ => False

instance : DecidablePred (IsCreate (ambient := ambient) (KemSK := KemSK)) := fun query => by
  rcases query with query | (query | query)
  · exact inferInstanceAs (Decidable False)
  · cases query <;> simp only [IsCreate] <;> infer_instance
  · exact inferInstanceAs (Decidable False)

private theorem reserved_create (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK)
    (pair : Pair KemSK) (future : List (Pair KemSK)) :
    (reserved baseImpl kem other (before.2.keys ++ pair :: future) (.inr (.inl .create))).run before =
      pure ((PqxdhLiveKemBirth.created before.2 pair).1, (before.1, (PqxdhLiveKemBirth.created before.2 pair).2)) := by
  simp [reserved, StateT.run]

private theorem noncreate_equal (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (Pair KemSK))
    (query : (Spec ambient KemSK).Domain) (noncreate : ¬ IsCreate query)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    (source baseImpl kem ambient other query).run before = (reserved baseImpl kem other pairs query).run before := by
  rcases query with query | (query | query) <;> try rfl
  cases query <;> simp_all [IsCreate, reserved, StateT.run]

private theorem noncreate_keys (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (query : (Spec ambient KemSK).Domain)
    (noncreate : ¬ IsCreate query) (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK)
    (result : (Spec ambient KemSK).Range query × (Auxiliary × PqxdhLiveKemBirth.Pool KemSK))
    (supported : result ∈ support ((source baseImpl kem ambient other query).run before)) :
    result.2.2.keys = before.2.keys := by
  rcases query with query | (query | query)
  · simp only [source, StateT.run, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    rfl
  · cases query with
    | create => exact False.elim (noncreate trivial)
    | reveal handle =>
      simp only [source, StateT.run, PqxdhLiveKemBirth.poolImpl, map_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
    | decapsulate handle ciphertext =>
      simp only [source, StateT.run, PqxdhLiveKemBirth.poolImpl, support_map] at supported
      obtain ⟨inner, actual, rfl⟩ := supported
      split at actual <;> simp only [mem_support_bind_iff, mem_support_pure_iff] at actual
      all_goals obtain ⟨answer, _, rfl⟩ := actual
      all_goals rfl
  · change result ∈ support (do
        let value ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps query)
        pure (value, before)) at supported
    rw [bind_pure_comp, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    rfl

/-- Native on-demand KEM creation and private reservation agree on complete results, all role state, generated pairs and private service histories. -/
theorem complete (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (work : OracleComp (Spec ambient KemSK) Result)
    (count : Nat) (bounded : work.IsQueryBoundP (IsCreate (ambient := ambient) (KemSK := KemSK)) count)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    EvalDistEq ((simulateQ (source baseImpl kem ambient other) work).run before)
      (samplePairs (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count >>= fun future =>
        (simulateQ (reserved baseImpl kem other (before.2.keys ++ future)) work).run before) := by
  induction work using OracleComp.inductionOn generalizing count before with
  | pure value =>
    simpa only [simulateQ_pure, StateT.run_pure] using
      (PqxdhLiveKemReservation.unused (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count (pure (value, before))).symm
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    change EvalDistEq ((source baseImpl kem ambient other query).run before >>= fun result =>
      (simulateQ (source baseImpl kem ambient other) (next result.1)).run result.2) _
    change EvalDistEq _ (samplePairs (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count >>= fun future =>
      (reserved baseImpl kem other (before.2.keys ++ future) query).run before >>= fun result =>
        (simulateQ (reserved baseImpl kem other (before.2.keys ++ future)) (next result.1)).run result.2)
    by_cases creates : IsCreate query
    · have queryEq : query = .inr (.inl .create) := by
        rcases query with query | (query | query)
        · exact False.elim creates
        · cases query <;> simp_all [IsCreate]
        · exact False.elim creates
      subst query
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (bounded.1.resolve_left (not_not.mpr creates)))
      rw [RegistrationNativeKemInterface.create_source, samplePairs]
      simp only [bind_assoc, bind_map_left, pure_bind]
      refine EvalDistEq.bind_right _ fun pair => ?_
      simp only [reserved_create, pure_bind]
      simpa only [PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, List.append_assoc, List.singleton_append] using
        ih (PqxdhLiveKemBirth.created before.2 pair).1 count
          (by simpa [IsCreate] using bounded.2 (PqxdhLiveKemBirth.created before.2 pair).1)
          (before.1, (PqxdhLiveKemBirth.created before.2 pair).2)
    · have stepEq (future : List (Pair KemSK)) := noncreate_equal baseImpl kem other (before.2.keys ++ future) query
        creates before
      simp_rw [← stepEq]
      refine EvalDistEq.trans ?_ (PqxdhSecretInputKdf.evalSPMF_sample_comm
        (samplePairs (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count)
        ((source baseImpl kem ambient other query).run before) _).symm
      refine OracleComp.EvalDistEq.bind_congr_of_support _ fun result actual => ?_
      simpa only [noncreate_keys baseImpl kem other query creates before result actual] using
        ih result.1 count (by simpa [creates] using bounded.2 result.1) result.2

/-- Selecting a genuine future owner creation moves only its actual generator, preserving the complete native continuation and all private states. -/
theorem target_first (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (work : OracleComp (Spec ambient KemSK) Result)
    (count : Nat) (target : Fin (count + 1)) (bounded : work.IsQueryBoundP (IsCreate (ambient := ambient) (KemSK := KemSK)) (count + 1))
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    EvalDistEq ((simulateQ (source baseImpl kem ambient other) work).run before)
      (do let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
          let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
          (simulateQ (reserved baseImpl kem other
            (before.2.keys ++ List.ofFn (target.insertNth chosen others))) work).run before) := by
  refine (complete baseImpl kem other work (count + 1) bounded before).trans ?_
  simp only [PqxdhLiveKemSelection.family_list, bind_map_left]
  exact PqxdhLiveKemSelection.target_first (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count target
    (fun family => (simulateQ (reserved baseImpl kem other (before.2.keys ++ List.ofFn family)) work).run before)

end BeaconcryptCore.Computational.RegistrationNativeKemReservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReservation.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReservation.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReservation.target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReservation.target_first
