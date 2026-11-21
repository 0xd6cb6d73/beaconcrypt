-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution

/-! A failed selected generation attempt never yields a learned public target key. The exact actual attempt counter remains threaded through all subsequent native controllers and failed signatures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaGenerationGhost (State step advance)
open RegistrationNativeMldsaProgram (Spec)
variable {V S : Type} (source : Source)

def Empty (before : State × Pool source) : Prop :=
  before.1.attempts = before.2.attempts ∧ before.1.publicKey = none

private theorem generate_empty (selected : Nat) (tape : List (Option (Credential source)))
    (failed : tape[selected]? = some none) (before : State × Pool source) (empty : Empty source before) :
    Empty source
      (step source selected (.inr .generate)
          (RegistrationNativeMldsaOpaque.birth source before.2 ((tape[before.2.attempts]?).getD none, 0)).1 before.1,
        (RegistrationNativeMldsaOpaque.birth source before.2 ((tape[before.2.attempts]?).getD none, 0)).2) := by
  constructor
  · change before.1.attempts + 1 = _
    rw [RegistrationNativeMldsaOpaque.birth_attempt, empty.1]
  · by_cases at_selected : before.1.attempts = selected
    · have table_selected : before.2.attempts = selected := empty.1.symm.trans at_selected
      simp only [step, advance, at_selected, ite_true, table_selected, failed, Option.getD_some,
        RegistrationNativeMldsaOpaque.birth, Option.map_none]
    · simp only [step, advance, at_selected, ite_false, empty.2]

/-- Every actual eager source step preserves absence of the failed selected target. -/
theorem query_empty (selected : Nat) (tape : List (Option (Credential source)))
    (failed : tape[selected]? = some none) (query : (Spec (handleSource source)).Domain) (before : State × Pool source)
    (empty : Empty source before) (result : (Spec (handleSource source)).Range query × (State × Pool source))
    (supported : result ∈ support ((RegistrationNativeMldsaGhostEager.handler source selected tape query).run before)) :
    Empty source result.2 := by
  change result ∈ support ((fun inner => (inner.1, (step source selected query inner.1 before.1, inner.2))) <$>
    (RegistrationNativeMldsaEager.handler source tape query).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  cases query with
  | inl coin =>
      simp only [RegistrationNativeMldsaEager.handler, RegistrationNativeMldsaZeroSource.handler,
        StateT.run_lift, bind_pure_comp, support_map] at possible
      obtain ⟨reply, _drawn, same⟩ := possible
      cases same
      exact empty
  | inr query => cases query with
    | generate =>
        have same : inner = RegistrationNativeMldsaOpaque.birth source before.2 ((tape[before.2.attempts]?).getD none, 0) :=
          Set.mem_singleton_iff.mp possible
        cases same
        exact generate_empty source selected tape failed before empty
    | sign handle request =>
        simp only [RegistrationNativeMldsaEager.handler, RegistrationNativeMldsaZeroSource.handler,
          RegistrationNativeMldsaZeroSource.capability, StateT.run] at possible
        cases found : before.2.keys[handle.secret]? with
        | none =>
            simp only [found, support_pure, Set.mem_singleton_iff] at possible
            cases possible
            exact empty
        | some key =>
            simp only [found] at possible
            split at possible
            next =>
              simp only [support_map] at possible
              obtain ⟨reply, _signed, same⟩ := possible
              cases same
              exact empty
            next =>
              simp only [support_pure, Set.mem_singleton_iff] at possible
              cases possible
              exact empty

/-- Every complete adaptive eager source execution retains absence of the failed selected key. -/
theorem program_empty (selected : Nat) (tape : List (Option (Credential source)))
    (failed : tape[selected]? = some none) (work : OracleComp (Spec (handleSource source)) V)
    (before : State × Pool source) (empty : Empty source before) (result : V × (State × Pool source))
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaGhostEager.handler source selected tape) work).run before)) :
    Empty source result.2 :=
by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact empty
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact ih middle.1 middle.2 (query_empty source selected tape failed query before empty middle queried) continued

/-- Any complete tracked native controller preserves the same failed-target absence. -/
theorem execute_empty (selected : Nat) (tape : List (Option (Credential source)))
    (failed : tape[selected]? = some none)
    (work : StateT S (OracleComp (Spec (handleSource source))) V)
    (before : RegistrationNativeMldsaGhostEagerExecution.State (S := S) source) (empty : Empty source before.2)
    (result : V × RegistrationNativeMldsaGhostEagerExecution.State (S := S) source)
    (supported : result ∈ support ((RegistrationNativeMldsaGhostEagerExecution.execute source selected tape work).run before)) :
    Empty source result.2.2 := by
  rw [RegistrationNativeMldsaGhostEagerExecution.joint, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact program_empty source selected tape failed (work.run before.1) before.2 empty inner possible
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure.query_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure.query_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure.program_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure.program_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure.execute_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure.execute_empty
