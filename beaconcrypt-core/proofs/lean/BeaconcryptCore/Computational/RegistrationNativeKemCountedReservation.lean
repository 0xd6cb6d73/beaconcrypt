-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample

/-! Future private recipient rows are reserved together with their actual source draw costs. A row and its cost become visible only at the actual create request; unused rows change no native counter. This is a complete adaptive execution coupling, not a postselected public-key argument. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeKemCountedProgram (Spec handler evaluate)
open RegistrationNativeKemCountedRecipientSample (Draw generation)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def family (setup : Setup base KemSK) : (count : Nat) → ProbComp (Fin count → Draw KemSK)
  | 0 => pure Fin.elim0
  | count + 1 => do
      let generated ← generation setup
      let rest ← family setup count
      pure (Fin.cons generated rest)

noncomputable def sample (setup : Setup base KemSK) (count : Nat) : ProbComp (List (Draw KemSK)) :=
  List.ofFn <$> family setup count

private theorem sample_zero (setup : Setup base KemSK) : sample setup 0 = pure [] := by
  simp only [sample, family, map_pure, List.ofFn_zero]
private theorem sample_succ (setup : Setup base KemSK) (count : Nat) : sample setup (count + 1) = (do
    let drawn ← generation setup
    let rest ← sample setup count
    pure (drawn :: rest)) := by
  simp only [sample, family, map_bind, List.ofFn_succ, bind_pure_comp, Functor.map_map, Fin.cons_zero, Fin.cons_succ]

noncomputable def reserved (setup : Setup base KemSK) (tape : List (Draw KemSK)) :
    QueryImpl (Spec KemSK) (StateT (Pool KemSK) ProbComp) := fun query before =>
  match query with
  | .inr (.inl .create) => match tape[before.keys.length]? with
      | none => (handler setup.baseImpl setup.kem (.inr (.inl .create))).run before
      | some drawn => pure (let result := PqxdhLiveKemBirth.created before drawn.1
          ((result.1, drawn.2), result.2))
  | query => (handler setup.baseImpl setup.kem query).run before

def IsCreate : (Spec KemSK).Domain → Prop
  | .inr (.inl .create) => True
  | _ => False
instance : DecidablePred (IsCreate (KemSK := KemSK)) := fun query => by
  rcases query with uniform | (pool | key)
  · exact inferInstanceAs (Decidable False)
  · cases pool <;> simp only [IsCreate] <;> infer_instance
  · exact inferInstanceAs (Decidable False)

private theorem reserved_create (setup : Setup base KemSK) (before : Pool KemSK)
    (past : List (Draw KemSK)) (past_length : past.length = before.keys.length)
    (drawn : Draw KemSK) (future : List (Draw KemSK)) :
    (reserved setup (past ++ drawn :: future) (.inr (.inl .create))).run before =
      pure (let result := PqxdhLiveKemBirth.created before drawn.1
        ((result.1, drawn.2), result.2)) := by
  simp only [reserved, StateT.run, ← past_length, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

private theorem noncreate_equal (setup : Setup base KemSK) (tape : List (Draw KemSK))
    (query : (Spec KemSK).Domain) (noncreate : ¬ IsCreate query) :
    handler setup.baseImpl setup.kem query = reserved setup tape query := by
  rcases query with uniform | (pool | key) <;> try rfl
  cases pool with
  | create => exact (noncreate trivial).elim
  | decapsulate _ _ => rfl
  | reveal _ => rfl

private theorem draw_keys (setup : Setup base KemSK)
    (query : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Domain)
    (noncreate : query ≠ .inl .create) (before : Pool KemSK)
    (result : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Range query × Pool KemSK)
    (supported : result ∈ support ((RegistrationNativeKemCountedCapability.draw setup.baseImpl setup.kem query).run before)) :
    result.2.keys = before.keys := by
  cases query with
  | inr key =>
      simp only [RegistrationNativeKemCountedCapability.draw, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _sampled, returned⟩ := supported
      cases returned
      rfl
  | inl query =>
      cases query with
      | create => exact (noncreate rfl).elim
      | reveal handle =>
          simp only [RegistrationNativeKemCountedCapability.draw, PqxdhLiveKemBirth.poolImpl, StateT.run, support_pure,
            Set.mem_singleton_iff] at supported
          cases supported
          rfl
      | decapsulate handle ciphertext =>
          simp only [RegistrationNativeKemCountedCapability.draw, PqxdhLiveKemBirth.poolImpl, StateT.run] at supported
          split at supported <;> simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          all_goals obtain ⟨reply, _decapsulated, returned⟩ := supported
          all_goals cases returned
          all_goals rfl

private theorem noncreate_keys (setup : Setup base KemSK) (query : (Spec KemSK).Domain)
    (noncreate : ¬ IsCreate query) (before : Pool KemSK) (result : (Spec KemSK).Range query × Pool KemSK)
    (supported : result ∈ support ((handler setup.baseImpl setup.kem query).run before)) :
    result.2.keys = before.keys := by
  cases query with
  | inl uniform =>
      simp only [handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _sampled, returned⟩ := supported
      cases returned
      rfl
  | inr query =>
      have prior : (result.1.1, result.2) ∈ support ((RegistrationNativeKemCountedCapability.draw setup.baseImpl setup.kem query).run before) := by
        rw [← RegistrationNativeKemCountedCapability.actual_forget, support_map]
        exact Set.mem_image_of_mem _ supported
      apply draw_keys setup query _ before (result.1.1, result.2) prior
      intro same
      subst query
      exact noncreate trivial

/-- Lazy actual key generation and joint private row/cost reservation preserve the entire adaptive execution distribution. -/
theorem complete (setup : Setup base KemSK) (work : OracleComp (Spec KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) count)
    (before : Pool KemSK) (past : List (Draw KemSK)) (past_length : past.length = before.keys.length) :
    EvalDistEq (evaluate setup.baseImpl setup.kem work before)
      (sample setup count >>= fun future => (simulateQ (reserved setup (past ++ future)) work).run before) := by
  induction work using OracleComp.inductionOn generalizing count before past with
  | pure value =>
      simpa only [evaluate, simulateQ_pure, StateT.run_pure] using
        (OracleComp.EvalDistEq.bind_const (sample setup count) (pure (value, before))).symm
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      change EvalDistEq
        ((handler setup.baseImpl setup.kem query).run before >>= fun result => evaluate setup.baseImpl setup.kem (next result.1) result.2)
        (sample setup count >>= fun future => (reserved setup (past ++ future) query).run before >>= fun result =>
          (simulateQ (reserved setup (past ++ future)) (next result.1)).run result.2)
      by_cases creates : IsCreate query
      · have selected : query = .inr (.inl .create) := by
          rcases query with uniform | (pool | key)
          · exact creates.elim
          · cases pool <;> simp_all only [IsCreate]
          · exact creates.elim
        subst query
        have positive : 0 < count := bounded.1.resolve_left (not_not.mpr creates)
        cases count with
        | zero => omega
        | succ count =>
            rw [handler, RegistrationNativeKemCountedRecipientSample.actual_create, sample_succ]
            simp only [bind_assoc, bind_map_left, pure_bind]
            apply EvalDistEq.bind_right
            intro drawn
            simp only [reserved_create setup before past past_length, pure_bind]
            have after := ih ((PqxdhLiveKemBirth.created before drawn.1).1, drawn.2) count
              (by simpa only [IsCreate, ite_true, Nat.add_sub_cancel] using bounded.2 ((PqxdhLiveKemBirth.created before drawn.1).1, drawn.2))
              (PqxdhLiveKemBirth.created before drawn.1).2 (past ++ [drawn])
              (by simp only [List.length_append, List.length_singleton, past_length,
                PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, List.length_append])
            simpa only [List.append_assoc, List.singleton_append] using after
      · have step (future : List (Draw KemSK)) := noncreate_equal setup (past ++ future) query creates
        simp_rw [← step]
        refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap (sample setup count)
          ((handler setup.baseImpl setup.kem query).run before) _).symm
        apply OracleComp.EvalDistEq.bind_congr_of_support
        intro result supported
        exact ih result.1 count (by simpa only [creates, ite_false] using bounded.2 result.1)
          result.2 past (past_length.trans (congrArg List.length (noncreate_keys setup query creates before result supported)).symm)
/-- A fixed future creation ordinal may be sampled first with its exact private source cost, preserving every complete continuation. -/
theorem family_target_first (setup : Setup base KemSK) (count : Nat) (target : Fin (count + 1))
    (next : (Fin (count + 1) → Draw KemSK) → ProbComp Value) :
    EvalDistEq (family setup (count + 1) >>= next)
      (do let chosen ← generation setup
          let others ← family setup count
          next (target.insertNth chosen others)) := by
  induction count with
  | zero =>
      have target_zero : target = 0 := by apply Fin.ext; omega
      subst target
      simp only [family, bind_assoc, pure_bind, Fin.insertNth_zero']
      rfl
  | succ count ih =>
      induction target using Fin.cases with
      | zero =>
          simp only [family, Fin.insertNth_zero', bind_assoc, pure_bind]
          rfl
      | succ target =>
          have step : EvalDistEq (family setup (count + 1 + 1) >>= next)
              (do let first ← generation setup
                  let chosen ← generation setup
                  let others ← family setup count
                  next (Fin.cons first (target.insertNth chosen others))) := by
            change EvalDistEq ((do
              let first ← generation setup
              let others ← family setup (count + 1)
              pure (Fin.cons first others)) >>= next) _
            simp only [bind_assoc, pure_bind]
            apply EvalDistEq.bind_right
            intro first
            exact ih target (fun rest => next (Fin.cons first rest))
          refine step.trans ((OracleComp.EvalDistEq.bind_bind_swap (generation setup) (generation setup)
            (fun first chosen => do
              let others ← family setup count
              next (Fin.cons first (target.insertNth chosen others)))).trans ?_)
          simp only [family, Fin.insertNth_succ_cons, bind_assoc, pure_bind]
          exact EvalDistEq.rfl

/-- Actual bounded lazy creation agrees with its complete chosen-ordinal-first reservation, retaining native costs and complete private histories. -/
theorem target_first (setup : Setup base KemSK) (work : OracleComp (Spec KemSK) Value)
    (count : Nat) (target : Fin (count + 1))
    (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) (count + 1))
    (before : Pool KemSK) (past : List (Draw KemSK)) (past_length : past.length = before.keys.length) :
    EvalDistEq (evaluate setup.baseImpl setup.kem work before)
      (do let chosen ← generation setup
          let others ← family setup count
          (simulateQ (reserved setup (past ++ List.ofFn (target.insertNth chosen others))) work).run before) := by
  refine (complete setup work (count + 1) bounded before past past_length).trans ?_
  simp only [sample, bind_map_left]
  exact family_target_first setup count target
    (fun future => (simulateQ (reserved setup (past ++ List.ofFn future)) work).run before)

end BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation.family_target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation.family_target_first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation.target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation.target_first
