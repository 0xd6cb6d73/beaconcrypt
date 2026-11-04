-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaEager

/-! A public analysis ghost learns the selected generation attempt's public key only from its actual successful reply. Every failed generation still advances the ordinal. Tracking is an ordinary free-program transformation; it receives neither a future key nor any private signing key, and erasing it preserves the literal source program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaProgram (Spec)
variable {Value : Type} (source : Source)

structure State where
  attempts : Nat := 0
  publicKey : Option RegistrationNativeMldsaEuf.PublicKey := none

def advance (selected : Nat) (before : State)
    (generated : Option (Credential (handleSource source))) : State :=
  ⟨before.attempts + 1,
    if before.attempts = selected then generated.map Credential.publicKey else before.publicKey⟩

def step (selected : Nat) (query : (Spec (handleSource source)).Domain)
    (reply : (Spec (handleSource source)).Range query) (before : State) : State :=
  match query with
  | .inr .generate => advance source selected before reply.1
  | _ => before

def handler (selected : Nat) : QueryImpl (Spec (handleSource source)) (StateT State (OracleComp (Spec (handleSource source)))) :=
  fun query before => (fun reply => (reply, step source selected query reply before)) <$> (Spec (handleSource source)).query query

def run (selected : Nat) (work : OracleComp (Spec (handleSource source)) Value) (before : State) :
    OracleComp (Spec (handleSource source)) (Value × State) := (simulateQ (handler source selected) work).run before

private theorem run_bind (selected : Nat) (query : (Spec (handleSource source)).Domain)
    (next : (Spec (handleSource source)).Range query → OracleComp (Spec (handleSource source)) Value) (before : State) :
    run source selected ((Spec (handleSource source)).query query >>= next) before = (do
      let reply ← (Spec (handleSource source)).query query
      run source selected (next reply) (step source selected query reply before)) := by
  simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun reply => (reply, step source selected query reply before)) <$>
      ((Spec (handleSource source)).query query : OracleComp (Spec (handleSource source)) _) >>= fun middle =>
      (simulateQ (handler source selected) (next middle.1)).run middle.2) = _
  rw [bind_map_left]

/-- Erasing only the public generation ghost leaves the original complete free program, with the same primitive requests and optional replies. -/
theorem erase (selected : Nat) (work : OracleComp (Spec (handleSource source)) Value) (before : State) :
    Prod.fst <$> run source selected work before = work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [run_bind, map_bind]
      simp_rw [ih]

/-- The selected public key is learned at exactly its actual generation reply, while the source private count is ignored. -/
theorem generate (selected : Nat) (before : State)
    (generated : Option (Credential (handleSource source))) (count : Nat) :
    step source selected (.inr .generate) (generated, count) before =
      ⟨before.attempts + 1, if before.attempts = selected then generated.map Credential.publicKey else before.publicKey⟩ := rfl

/-- A failed generation consumes its real attempt ordinal and leaves the selected key absent. -/
theorem failed (selected : Nat) (before : State) (at_selected : before.attempts = selected) (count : Nat) :
    step source selected (.inr .generate) (none, count) before = ⟨before.attempts + 1, none⟩ := by
  simp only [step, advance, at_selected, ite_true, Option.map_none]

/-- The ghost's count-independent transition commutes with the checked primitive accounting normalization. -/
theorem zero_step (selected : Nat) (query : RegistrationNativeMldsaCapability.Request (handleSource source))
    (reply : (RegistrationNativeMldsaCapability.Spec (handleSource source)).Range query) (before : State) :
    step source selected (.inr query) (reply.1, 0) before = step source selected (.inr query) reply before := by
  cases query <;> rfl

/-- Tracking charges exactly the original predicate-selected primitive slots and introduces no new source query. -/
theorem bounded (selected : Nat) (work : OracleComp (Spec (handleSource source)) Value)
    (predicate : (Spec (handleSource source)).Domain → Prop) [DecidablePred predicate]
    (count : Nat) (bound : work.IsQueryBoundP predicate count) (before : State) :
    (run source selected work before).IsQueryBoundP predicate count := by
  apply bound.simulateQ_run_StateT_of_step _ before
  intro query current
  simp only [handler, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  by_cases active : predicate query
  · simp only [active, ite_true, true_implies]
    omega
  · simp only [active, false_implies]

/-- Count normalization and public generation tracking commute, because the ghost reads only the actual optional public reply. -/
theorem normalized (selected : Nat) (work : OracleComp (Spec (handleSource source)) Value) (before : State) :
    run source selected (RegistrationNativeMldsaCountMap.transform work) before =
      RegistrationNativeMldsaCountMap.transform (run source selected work before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [RegistrationNativeMldsaCountMap.transform, simulateQ_pure, run, StateT.run_pure]
  | query_bind query next ih =>
      simp only [run, RegistrationNativeMldsaCountMap.transform] at ih
      cases query with
      | inl coin =>
          simp only [RegistrationNativeMldsaCountMap.transform, simulateQ_bind, simulateQ_spec_query,
            RegistrationNativeMldsaCountMap.translation, run, StateT.run_bind]
          change ((handler source selected (.inl coin)).run before >>= fun middle =>
            (simulateQ (handler source selected)
              (simulateQ RegistrationNativeMldsaCountMap.translation (next middle.1))).run middle.2) = _
          simp only [handler, StateT.run, bind_map_left, simulateQ_map,
            simulateQ_spec_query, RegistrationNativeMldsaCountMap.translation]
          apply bind_congr
          intro reply
          exact ih reply _
      | inr request =>
          simp only [RegistrationNativeMldsaCountMap.transform, simulateQ_bind, simulateQ_spec_query,
            RegistrationNativeMldsaCountMap.translation, run, simulateQ_map, StateT.run_bind,
            StateT.run_map]
          simp only [handler, StateT.run, bind_map_left, Functor.map_map,
            simulateQ_map, simulateQ_spec_query, RegistrationNativeMldsaCountMap.translation,
            zero_step]
          apply bind_congr
          intro reply
          exact ih (reply.1, 0) _
end BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.generate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.failed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.zero_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.zero_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.bounded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost.normalized
