-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource
import BeaconcryptCore.Computational.PqxdhSecretInputKdf

/-! Bounded actual ML generation may reserve a private tape of optional source results before the adaptive client. Failed generation is a sampled None result and still consumes its actual attempt ordinal. Future results remain interpreter-private, and no public-key or secret-key injectivity is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaEager
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource birth)
variable {Value : Type} (source : Source)

noncomputable def family : (count : Nat) → ProbComp (Fin count → Option (Credential source))
  | 0 => pure Fin.elim0
  | count + 1 => do
      let generated ← RegistrationNativeMldsa.generate source
      let rest ← family count
      pure (Fin.cons generated rest)

noncomputable def sample (count : Nat) : ProbComp (List (Option (Credential source))) := List.ofFn <$> family source count

private theorem sample_zero : sample source 0 = pure [] := by
  simp only [sample, family, map_pure, List.ofFn_zero]
private theorem sample_succ (count : Nat) : sample source (count + 1) = (do
    let generated ← RegistrationNativeMldsa.generate source
    let rest ← sample source count
    pure (generated :: rest)) := by
  simp only [sample, family, map_bind, List.ofFn_succ, bind_pure_comp, Functor.map_map, Fin.cons_zero, Fin.cons_succ]

/-- A private optional-key tape contains exactly one real source result per generation attempt, including failures. -/
theorem sample_length (count : Nat) (future : List (Option (Credential source)))
    (supported : future ∈ support (sample source count)) : future.length = count := by
  simp only [sample, support_map] at supported
  obtain ⟨values, _sampled, rfl⟩ := supported
  exact List.length_ofFn

noncomputable def handler (tape : List (Option (Credential source))) :
    QueryImpl (RegistrationNativeMldsaProgram.Spec (handleSource source)) (StateT (Pool source) ProbComp)
  | .inr .generate => fun before => pure (birth source before ((tape[before.attempts]?).getD none, 0))
  | query => RegistrationNativeMldsaZeroSource.handler source query

def IsGenerate : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain → Prop
  | .inr .generate => True
  | _ => False

instance : DecidablePred (IsGenerate source) := fun query => by
  cases query with
  | inl coin => exact inferInstanceAs (Decidable False)
  | inr query => cases query <;> simp only [IsGenerate] <;> infer_instance

private theorem generate (before : Pool source) :
    (RegistrationNativeMldsaZeroSource.handler source (.inr .generate)).run before =
      (fun generated => birth source before (generated, 0)) <$> RegistrationNativeMldsa.generate source := rfl

private theorem eager_generate (past : List (Option (Credential source))) (before : Pool source)
    (past_length : past.length = before.attempts) (generated : Option (Credential source))
    (future : List (Option (Credential source))) :
    (handler source (past ++ generated :: future) (.inr .generate)).run before = pure (birth source before (generated, 0)) := by
  simp only [handler, StateT.run, ← past_length, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

private theorem non_generate (tape : List (Option (Credential source)))
    (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) (other : ¬ IsGenerate source query) :
    RegistrationNativeMldsaZeroSource.handler source query = handler source tape query := by
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | generate => exact (other trivial).elim
    | sign _ _ => rfl

private theorem attempts (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain)
    (other : ¬ IsGenerate source query) (before : Pool source)
    (result : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Range query × Pool source)
    (supported : result ∈ support ((RegistrationNativeMldsaZeroSource.handler source query).run before)) :
    result.2.attempts = before.attempts := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeMldsaZeroSource.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _sampled, rfl⟩ := supported
      rfl
  | inr query => cases query with
    | generate => exact (other trivial).elim
    | sign handle request =>
        simp only [RegistrationNativeMldsaZeroSource.handler, RegistrationNativeMldsaZeroSource.capability, StateT.run] at supported
        cases found : before.keys[handle.secret]? with
        | none =>
            simp only [found, support_pure, Set.mem_singleton_iff] at supported
            cases supported
            rfl
        | some key =>
            simp only [found] at supported
            split at supported
            next =>
              simp only [support_map] at supported
              obtain ⟨reply, _signed, rfl⟩ := supported
              rfl
            next =>
              simp only [support_pure, Set.mem_singleton_iff] at supported
              cases supported
              rfl

/-- Reserving unused optional generation results changes no complete evaluated continuation. -/
theorem sample_unused (count : Nat) (work : ProbComp Value) :
    EvalDistEq (sample source count >>= fun _ => work) work := OracleComp.EvalDistEq.bind_const _ work

/-- Actual lazy generation and private eager optional-key reservation have the same full adaptive execution distribution. -/
theorem complete (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (IsGenerate source) count)
    (before : Pool source) (past : List (Option (Credential source))) (past_length : past.length = before.attempts) :
    EvalDistEq (RegistrationNativeMldsaZeroSource.evaluate source work before)
      (sample source count >>= fun future => (simulateQ (handler source (past ++ future)) work).run before) := by
  induction work using OracleComp.inductionOn generalizing count before past with
  | pure value =>
      simpa only [RegistrationNativeMldsaZeroSource.evaluate, simulateQ_pure, StateT.run_pure] using
        (sample_unused source count (pure (value, before))).symm
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      change EvalDistEq
        ((RegistrationNativeMldsaZeroSource.handler source query).run before >>= fun result =>
          RegistrationNativeMldsaZeroSource.evaluate source (next result.1) result.2)
        (sample source count >>= fun future => (handler source (past ++ future) query).run before >>= fun result =>
          (simulateQ (handler source (past ++ future)) (next result.1)).run result.2)
      by_cases creates : IsGenerate source query
      · have selected : query = .inr .generate := by
          cases query with
          | inl coin => exact creates.elim
          | inr query => cases query with
            | generate => rfl
            | sign _ _ => exact creates.elim
        subst query
        have positive : 0 < count := bounded.1.resolve_left (not_not.mpr creates)
        cases count with
        | zero => omega
        | succ count =>
            rw [generate, sample_succ]
            simp only [bind_assoc, bind_map_left, pure_bind]
            apply EvalDistEq.bind_right
            intro generated
            simp only [eager_generate source past before past_length, pure_bind]
            have after := ih (birth source before (generated, 0)).1 count
              (by simpa only [IsGenerate, ite_true, Nat.add_sub_cancel] using bounded.2 (birth source before (generated, 0)).1)
              (birth source before (generated, 0)).2 (past ++ [generated])
              (by simp only [List.length_append, List.length_singleton, past_length, RegistrationNativeMldsaOpaque.birth_attempt])
            simpa only [List.append_assoc, List.singleton_append] using after
      · have step (future : List (Option (Credential source))) := non_generate source (past ++ future) query creates
        simp_rw [← step]
        apply EvalDistEq.trans _ (PqxdhSecretInputKdf.evalSPMF_sample_comm (sample source count)
          ((RegistrationNativeMldsaZeroSource.handler source query).run before) _).symm
        apply OracleComp.EvalDistEq.bind_congr_of_support
        intro result supported
        have unchanged := attempts source query creates before result supported
        exact ih result.1 count (by simpa only [creates, ite_false] using bounded.2 result.1)
          result.2 past (past_length.trans unchanged.symm)

/-- Any generation-attempt result, including None, can be sampled first independently of all other reserved results. -/
theorem family_target_first (count : Nat) (target : Fin (count + 1))
    (next : (Fin (count + 1) → Option (Credential source)) → ProbComp Value) :
    EvalDistEq (family source (count + 1) >>= next)
      (do
        let generated ← RegistrationNativeMldsa.generate source
        let rest ← family source count
        next (target.insertNth generated rest)) := by
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
          have step : EvalDistEq (family source (count + 1 + 1) >>= next)
              (do
                let first ← RegistrationNativeMldsa.generate source
                let chosen ← RegistrationNativeMldsa.generate source
                let rest ← family source count
                next (Fin.cons first (target.insertNth chosen rest))) := by
            change EvalDistEq ((do
              let first ← RegistrationNativeMldsa.generate source
              let rest ← family source (count + 1)
              pure (Fin.cons first rest)) >>= next) _
            simp only [bind_assoc, pure_bind]
            refine EvalDistEq.bind_right _ fun first => ?_
            exact ih target (fun rest => next (Fin.cons first rest))
          refine step.trans ((PqxdhSecretInputKdf.evalSPMF_sample_comm
            (RegistrationNativeMldsa.generate source) (RegistrationNativeMldsa.generate source)
            (fun first chosen => do
              let rest ← family source count
              next (Fin.cons first (target.insertNth chosen rest)))).trans ?_)
          simp only [family, Fin.insertNth_succ_cons, bind_assoc, pure_bind]
          rfl

/-- The complete bounded execution can move any reserved generation attempt to the ordinary single-key challenger's first draw. -/
theorem complete_target_first
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (IsGenerate source) (count + 1))
    (target : Fin (count + 1)) :
    EvalDistEq (RegistrationNativeMldsaZeroSource.evaluate source work {})
      (do
        let generated ← RegistrationNativeMldsa.generate source
        let rest ← family source count
        (simulateQ (handler source (List.ofFn (target.insertNth generated rest))) work).run {}) := by
  refine (complete source work (count + 1) bounded {} [] rfl).trans ?_
  simpa only [sample, bind_map_left, List.nil_append] using
    family_target_first source count target
      (fun values => (simulateQ (handler source (List.ofFn values)) work).run {})
end BeaconcryptCore.Computational.RegistrationNativeMldsaEager

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEager.sample_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEager.sample_length

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEager.sample_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEager.sample_unused

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEager.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEager.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEager.family_target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEager.family_target_first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEager.complete_target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEager.complete_target_first
