-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost
import BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage

/-! Every successful private-table birth at a selected ordinal is the public key actually learned by the public generation ghost. The invariant uses actual birth provenance to exclude an earlier row at the currently attempted ordinal; failed births are counted and no public-key injectivity is needed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource birth)
open RegistrationNativeMldsaGenerationGhost (State step advance)
open RegistrationNativeMldsaBirthProvenance (Provenance)
open RegistrationNativeMldsaProgram (Spec)
variable {Value : Type} (source : Source)

def Rows (selected : Nat) (ghost : State) (pool : Pool source) : Prop :=
  ∀ (index : Nat) (key : Credential source), pool.keys[index]? = some key → pool.bornAt[index]? = some selected → ghost.publicKey = some key.publicKey

structure Safe (selected : Nat) (before : State × Pool source) : Prop where
  provenance : Provenance source before.2
  count : before.1.attempts = before.2.attempts
  rows : Rows source selected before.1 before.2

private theorem advanced_old (selected : Nat) (ghost : State) (pool : Pool source)
    (good : Provenance source pool) (count : ghost.attempts = pool.attempts) (rows : Rows source selected ghost pool)
    (generated : Option (Credential (handleSource source))) (index : Nat) (key : Credential source)
    (found : pool.keys[index]? = some key) (ordinal : pool.bornAt[index]? = some selected) :
    (advance source selected ghost generated).publicKey = some key.publicKey := by
  by_cases at_selected : ghost.attempts = selected
  · have earlier := good.earlier selected (List.mem_of_getElem? ordinal)
    omega
  · simp only [advance, at_selected, ite_false]
    exact rows index key found ordinal

private theorem birth_rows (selected : Nat) (ghost : State) (pool : Pool source)
    (good : Provenance source pool) (count : ghost.attempts = pool.attempts) (rows : Rows source selected ghost pool)
    (generated : Option (Credential source) × Nat) :
    Rows source selected
      (step source selected (.inr .generate) (birth source pool generated).1 ghost)
      (birth source pool generated).2 := by
  intro index key found ordinal
  rcases generated with ⟨generated, coins⟩
  cases generated with
  | none => exact advanced_old source selected ghost pool good count rows none index key found ordinal
  | some generated =>
      change (pool.keys ++ [generated])[index]? = some key at found
      change (pool.bornAt ++ [pool.attempts])[index]? = some selected at ordinal
      by_cases old : index < pool.keys.length
      · have old_birth : index < pool.bornAt.length := good.aligned ▸ old
        rw [List.getElem?_append_left old] at found
        rw [List.getElem?_append_left old_birth] at ordinal
        exact advanced_old source selected ghost pool good count rows _ index key found ordinal
      · have within := (List.getElem?_eq_some_iff.mp found).1
        simp only [List.length_append, List.length_singleton] at within
        have last : index = pool.keys.length := by omega
        subst index
        rw [List.getElem?_concat_length] at found
        have key_same : generated = key := Option.some.inj found
        rw [good.aligned, List.getElem?_concat_length] at ordinal
        have selected_here : ghost.attempts = selected := count.trans (Option.some.inj ordinal)
        simp only [step, advance, selected_here, ite_true, birth, Option.map_some]
        exact congrArg (fun credential : Credential source => some credential.publicKey) key_same

noncomputable def handler (selected : Nat) : QueryImpl (Spec (handleSource source)) (StateT (State × Pool source) ProbComp) :=
  fun query before => (fun result => (result.1, (step source selected query result.1 before.1, result.2))) <$>
    (RegistrationNativeMldsaTableProgram.handler source query).run before.2

/-- Every actual true-count primitive call retains complete selected-birth public-key provenance. -/
theorem query_safe (selected : Nat) (query : (Spec (handleSource source)).Domain) (before : State × Pool source)
    (safe : Safe source selected before) (result : (Spec (handleSource source)).Range query × (State × Pool source))
    (supported : result ∈ support ((handler source selected query).run before)) : Safe source selected result.2 := by
  change result ∈ support ((fun inner => (inner.1, (step source selected query inner.1 before.1, inner.2))) <$>
    (RegistrationNativeMldsaTableProgram.handler source query).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  have provenance := (RegistrationNativeMldsaBirthProvenance.step source query before.2 safe.provenance inner possible).1
  refine ⟨provenance, ?_, ?_⟩
  · cases query with
    | inl coin =>
        simp only [RegistrationNativeMldsaTableProgram.handler, StateT.run_lift, bind_pure_comp, support_map] at possible
        obtain ⟨reply, _drawn, same⟩ := possible
        cases same
        exact safe.count
    | inr query => cases query with
      | generate =>
          simp only [RegistrationNativeMldsaTableProgram.handler, RegistrationNativeMldsaOpaque.actual, StateT.run, support_map] at possible
          obtain ⟨generated, _drawn, same⟩ := possible
          cases same
          change before.1.attempts + 1 = _
          rw [RegistrationNativeMldsaOpaque.birth_attempt, safe.count]
      | sign handle request =>
          have unchanged := (RegistrationNativeMldsaBirthProvenance.step source (.inr (.sign handle request)) before.2 safe.provenance inner possible).2
          simpa only [step, RegistrationNativeMldsaEager.IsGenerate, ite_false, Nat.add_zero, ← safe.count] using unchanged.symm
  · cases query with
    | inl coin =>
        simp only [RegistrationNativeMldsaTableProgram.handler, StateT.run_lift, bind_pure_comp, support_map] at possible
        obtain ⟨reply, _drawn, same⟩ := possible
        cases same
        exact safe.rows
    | inr query => cases query with
      | generate =>
          simp only [RegistrationNativeMldsaTableProgram.handler, RegistrationNativeMldsaOpaque.actual, StateT.run, support_map] at possible
          obtain ⟨generated, _drawn, same⟩ := possible
          cases same
          exact birth_rows source selected before.1 before.2 safe.provenance safe.count safe.rows generated
      | sign handle request =>
          simp only [RegistrationNativeMldsaTableProgram.handler, RegistrationNativeMldsaOpaque.actual, StateT.run] at possible
          cases found : before.2.keys[handle.secret]? with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at possible
              cases possible
              exact safe.rows
          | some key =>
              simp only [found] at possible
              split at possible
              next =>
                simp only [support_map] at possible
                obtain ⟨reply, _signed, same⟩ := possible
                cases same
                exact safe.rows
              next =>
                simp only [support_pure, Set.mem_singleton_iff] at possible
                cases possible
                exact safe.rows

/-- A complete actual source continuation preserves any already reached joint birth/ghost invariant. -/
theorem program_keep (selected : Nat) (work : OracleComp (Spec (handleSource source)) Value)
    (before : State × Pool source) (initial : Safe source selected before)
    (result : Value × (State × Pool source))
    (supported : result ∈ support ((simulateQ (handler source selected) work).run before)) :
    Safe source selected result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (handler source selected) (Safe source selected)
    (query_safe source selected) work before initial result supported

/-- Actual joint executions from the empty source table derive the selected-generation ghost invariant. -/
theorem program_safe (selected : Nat) (work : OracleComp (Spec (handleSource source)) Value)
    (result : Value × (State × Pool source))
    (supported : result ∈ support ((simulateQ (handler source selected) work).run ({}, {}))) :
    Safe source selected result.2 := by
  apply PqxdhRecordLiftFlat.support_keep_oracle (handler source selected) (Safe source selected)
    (query_safe source selected) work ({}, {}) _ result supported
  exact ⟨⟨rfl, by intro ordinal impossible; cases impossible⟩, rfl,
    by intro index key impossible; cases index <;> cases impossible⟩

/-- A protected successful actual birth receipt identifies exactly the key learned by this public ghost. -/
theorem learned (selected : Nat) (before : State × Pool source) (safe : Safe source selected before)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (born : RegistrationNativeMldsaProtectedCoverage.BornKey source before.2 selected publicKey) :
    before.1.publicKey = some publicKey := by
  obtain ⟨index, key, found, ordinal, matching⟩ := born
  exact (safe.rows index key found ordinal).trans (congrArg some matching)

private theorem map_apply {S A B : Type} (observer : A → B) (work : StateT S ProbComp A) (before : S) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

/-- The concrete actual ghost/table handler is the literal standard stateful source composition. -/
theorem link (selected : Nat) :
    handler source selected = QueryImpl.Stateful.link
      (RegistrationNativeMldsaGenerationGhost.handler source selected)
      (RegistrationNativeMldsaTableProgram.handler source) := by
  funext query before
  rcases before with ⟨ghost, pool⟩
  have composed := QueryImpl.Stateful.link_impl_apply_run
    (RegistrationNativeMldsaGenerationGhost.handler source selected)
    (RegistrationNativeMldsaTableProgram.handler source) query ghost pool
  simp only [StateT.run] at composed
  rw [composed]
  simp only [RegistrationNativeMldsaGenerationGhost.handler,
    simulateQ_map, simulateQ_spec_query, map_apply, Functor.map_map]
  rfl

/-- Tracking the original free source program and interpreting its actual private table preserves the entire joint value, ghost and true-count source state. -/
theorem source_program (selected : Nat) (work : OracleComp (Spec (handleSource source)) Value)
    (before : State) (pool : Pool source) :
    (simulateQ (handler source selected) work).run (before, pool) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        RegistrationNativeMldsaTableProgram.evaluate source
          (RegistrationNativeMldsaGenerationGhost.run source selected work before) pool := by
  rw [link, QueryImpl.Stateful.simulateQ_link_run]
  rfl
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.query_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.program_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.program_keep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.program_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.learned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.learned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.link

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostRows.source_program
