-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEager
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState
import BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder

/-! Arbitrary native controllers interpreted with the actual selected-first eager table retain the selected-key ghost invariant. Dynamic key observation is bounded by fixed challenge-key observation using a shared source execution, not an adaptive independence assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaGhostState (track)
open RegistrationNativeMldsaStop (Observer monitor)
variable {S V Query Candidate : Type} {queries : OracleSpec Query} (source : Source)
private theorem map_apply {State A B : Type} (observer : A → B) (work : StateT State ProbComp A) (before : State) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

abbrev State := S × (RegistrationNativeMldsaGenerationGhost.State × Pool source)

noncomputable def execute (selected : Nat) (tape : List (Option (Credential source)))
    (work : StateT S (OracleComp (Spec (handleSource source))) V) :
    StateT (State (S := S) source) ProbComp V := fun before =>
  (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
    (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      ((track source selected work).run (before.1, before.2.1))).run before.2.2

/-- The tracked native lens is the exact full joint eager source interpretation. -/
theorem joint (selected : Nat) (tape : List (Option (Credential source)))
    (work : StateT S (OracleComp (Spec (handleSource source))) V) (before : State (S := S) source) :
    (execute source selected tape work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeMldsaGhostEager.handler source selected tape) (work.run before.1)).run before.2 := by
  rw [RegistrationNativeMldsaGhostEager.source_program]
  simp only [execute, track, StateT.run, simulateQ_map, map_apply, Functor.map_map]
  rfl

/-- Every complete source controller preserves the ghost's exact selected-key invariant. -/
theorem fixed (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (work : StateT S (OracleComp (Spec (handleSource source))) V) (before : State (S := S) source)
    (safe : RegistrationNativeMldsaGhostEager.Fixed source challenge.publicKey before.2)
    (result : V × State (S := S) source)
    (supported : result ∈ support ((execute source selected tape work).run before)) :
    RegistrationNativeMldsaGhostEager.Fixed source challenge.publicKey result.2.2 := by
  rw [joint, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaGhostEager.program_fixed source selected tape challenge chosen
    (work.run before.1) before.2 safe inner possible

def dynamic (observe : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate)) :
    Observer (spec := queries) (State := State (S := S) source) (Candidate := Candidate) :=
  fun query before reply after => after.2.1.publicKey.bind (fun publicKey => observe publicKey query before.1 reply after.1)

def constant (observe : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    Observer (spec := queries) (State := State (S := S) source) (Candidate := Candidate) :=
  fun query before reply after => observe publicKey query before.1 reply after.1

/-- On the actual selected-first table, a dynamically learned-key hit implies a fixed challenge-key hit at that identical source cut. -/
theorem observer_order
    (observe : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) (query : queries.Domain)
    (before after : State (S := S) source) (reply : queries.Range query)
    (safe : RegistrationNativeMldsaGhostEager.Fixed source publicKey after.2) :
    (dynamic source observe query before reply after).isSome = true →
      (constant source observe publicKey query before reply after).isSome = true := by
  cases learned : after.2.1.publicKey with
  | none => simp only [dynamic, learned, Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_implies]
  | some key =>
      have same := safe.2 key (by rw [learned]; exact Option.mem_some_self _)
      simp only [dynamic, constant, learned, Option.bind_some, same, imp_self]

/-- The complete dynamic learned-key monitor is bounded by the ordinary fixed-key monitor under the actual shared eager source execution. -/
theorem monitor_bound (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (handler : QueryImpl queries (StateT S (OracleComp (Spec (handleSource source)))))
    (observe : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (work : OracleComp queries V) (before : State (S := S) source)
    (safe : RegistrationNativeMldsaGhostEager.Fixed source challenge.publicKey before.2) :
    Pr{let result ← (simulateQ (monitor (fun query => execute source selected tape (handler query)) (dynamic source observe)) work).run (before, none)}[
      result.2.2.isSome = true] ≤
    Pr{let result ← (simulateQ (monitor (fun query => execute source selected tape (handler query)) (constant source observe challenge.publicKey)) work).run (before, none)}[
      result.2.2.isSome = true] := by
  apply RegistrationNativeMldsaMonitorOrder.bound _ _ _
    (fun current => RegistrationNativeMldsaGhostEager.Fixed source challenge.publicKey current.2) _ _ work before safe
  · intro query current result good supported
    exact fixed source selected tape challenge chosen (handler query) current good result supported
  · intro query current result good supported
    exact observer_order source observe challenge.publicKey query current result.2 result.1
      (fixed source selected tape challenge chosen (handler query) current good result supported)
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.observer_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.observer_order

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.monitor_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution.monitor_bound
