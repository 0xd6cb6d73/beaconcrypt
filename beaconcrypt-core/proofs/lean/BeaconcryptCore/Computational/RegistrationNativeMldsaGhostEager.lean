-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost

/-! The selected public-key ghost is coupled to the actual eager interpreter. Its counter equals the private table's attempt counter, and it can learn only the actual selected tape key. This invariant includes invalid signatures, optional failures and unused reserved entries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaGenerationGhost (State step advance)
open RegistrationNativeMldsaProgram (Spec)
variable {Value : Type} (source : Source)

private theorem map_apply {S A B : Type} (observer : A → B) (work : StateT S ProbComp A) (before : S) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

noncomputable def handler (selected : Nat) (tape : List (Option (Credential source))) :
    QueryImpl (Spec (handleSource source)) (StateT (State × Pool source) ProbComp) := fun query before =>
  (fun result => (result.1, (step source selected query result.1 before.1, result.2))) <$>
    (RegistrationNativeMldsaEager.handler source tape query).run before.2

def Fixed (publicKey : RegistrationNativeMldsaEuf.PublicKey) (before : State × Pool source) : Prop :=
  before.1.attempts = before.2.attempts ∧ ∀ key ∈ before.1.publicKey, key = publicKey

private theorem generate_fixed (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (before : State × Pool source) (fixed : Fixed source challenge.publicKey before) :
    Fixed source challenge.publicKey
      (step source selected (.inr .generate)
          (RegistrationNativeMldsaOpaque.birth source before.2 ((tape[before.2.attempts]?).getD none, 0)).1 before.1,
        (RegistrationNativeMldsaOpaque.birth source before.2 ((tape[before.2.attempts]?).getD none, 0)).2) := by
  constructor
  · change before.1.attempts + 1 = _
    rw [RegistrationNativeMldsaOpaque.birth_attempt, fixed.1]
  · intro key member
    by_cases at_selected : before.1.attempts = selected
    · have table_selected : before.2.attempts = selected := fixed.1.symm.trans at_selected
      simp only [step, advance, at_selected, ite_true, table_selected, chosen,
        Option.getD_some, RegistrationNativeMldsaOpaque.birth, Option.map_some,
        Option.mem_some_iff] at member
      exact member.symm
    · simp only [step, advance, at_selected, ite_false] at member
      exact fixed.2 key member

/-- Every actual eager primitive step preserves the selected-key ghost relation with the complete current source table. -/
theorem query_fixed (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (query : (Spec (handleSource source)).Domain) (before : State × Pool source)
    (fixed : Fixed source challenge.publicKey before)
    (result : (Spec (handleSource source)).Range query × (State × Pool source))
    (supported : result ∈ support ((handler source selected tape query).run before)) :
    Fixed source challenge.publicKey result.2 := by
  change result ∈ support ((fun inner => (inner.1, (step source selected query inner.1 before.1, inner.2))) <$>
    (RegistrationNativeMldsaEager.handler source tape query).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  cases query with
  | inl coin =>
      simp only [RegistrationNativeMldsaEager.handler, RegistrationNativeMldsaZeroSource.handler,
        StateT.run_lift, bind_pure_comp, support_map] at possible
      obtain ⟨reply, _sampled, same⟩ := possible
      cases same
      exact fixed
  | inr query => cases query with
    | generate =>
        have same : inner = RegistrationNativeMldsaOpaque.birth source before.2 ((tape[before.2.attempts]?).getD none, 0) :=
          Set.mem_singleton_iff.mp possible
        cases same
        exact generate_fixed source selected tape challenge chosen before fixed
    | sign handle request =>
        simp only [RegistrationNativeMldsaEager.handler, RegistrationNativeMldsaZeroSource.handler,
          RegistrationNativeMldsaZeroSource.capability, StateT.run] at possible
        cases found : before.2.keys[handle.secret]? with
        | none =>
            simp only [found, support_pure, Set.mem_singleton_iff] at possible
            cases possible
            exact fixed
        | some key =>
            simp only [found] at possible
            split at possible
            next =>
              simp only [support_map] at possible
              obtain ⟨reply, _signed, same⟩ := possible
              cases same
              exact fixed
            next =>
              simp only [support_pure, Set.mem_singleton_iff] at possible
              cases possible
              exact fixed

/-- The complete adaptive source interpretation retains the selected-key relation at every reached final table state. -/
theorem program_fixed (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (work : OracleComp (Spec (handleSource source)) Value) (before : State × Pool source)
    (fixed : Fixed source challenge.publicKey before) (result : Value × (State × Pool source))
    (supported : result ∈ support ((simulateQ (handler source selected tape) work).run before)) :
    Fixed source challenge.publicKey result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact fixed
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact ih middle.1 middle.2 (query_fixed source selected tape challenge chosen query before fixed middle queried) continued

/-- The concrete joint handler is precisely the standard stateful composition of the public ghost and actual eager source interpreter. -/
theorem link (selected : Nat) (tape : List (Option (Credential source))) :
    handler source selected tape = QueryImpl.Stateful.link
      (RegistrationNativeMldsaGenerationGhost.handler source selected)
      (RegistrationNativeMldsaEager.handler source tape) := by
  funext query before
  rcases before with ⟨ghost, pool⟩
  have composed := QueryImpl.Stateful.link_impl_apply_run
    (RegistrationNativeMldsaGenerationGhost.handler source selected)
    (RegistrationNativeMldsaEager.handler source tape) query ghost pool
  simp only [StateT.run] at composed
  rw [composed]
  simp only [RegistrationNativeMldsaGenerationGhost.handler,
    simulateQ_map, simulateQ_spec_query, map_apply, Functor.map_map]
  rfl

/-- The public tracking transformation and complete eager table interpreter retain the same joint value, ghost and private table state. -/
theorem source_program (selected : Nat) (tape : List (Option (Credential source)))
    (work : OracleComp (Spec (handleSource source)) Value) (before : State) (pool : Pool source) :
    (simulateQ (handler source selected tape) work).run (before, pool) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeMldsaEager.handler source tape)
          (RegistrationNativeMldsaGenerationGhost.run source selected work before)).run pool := by
  rw [link, QueryImpl.Stateful.simulateQ_link_run]
  rfl

/-- Every reached selected-first eager execution learns only the challenged public key, even though the source code did not know this key before generation. -/
theorem selected_fixed {count : Nat} (target : Fin (count + 1))
    (challenge : Credential source) (others : Fin count → Option (Credential source))
    (work : OracleComp (Spec (handleSource source)) Value) (result : Value × (State × Pool source))
    (supported : result ∈ support ((simulateQ (handler source target.val
      (List.ofFn (target.insertNth (some challenge) others))) work).run ({}, {}))) :
    Fixed source challenge.publicKey result.2 := by
  apply program_fixed source target.val _ challenge _ work ({}, {}) ⟨rfl, by intro key impossible; cases impossible⟩ result supported
  simp only [List.getElem?_ofFn, target.isLt, _root_.dite_true, Fin.eta, Fin.insertNth_apply_same]
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.query_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.query_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.program_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.program_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.link

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.source_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.selected_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager.selected_fixed
