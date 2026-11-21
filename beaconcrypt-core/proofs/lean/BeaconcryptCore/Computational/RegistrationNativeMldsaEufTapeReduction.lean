-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory

/-! A finite chosen-attempt reduction to the ordinary complete-request ML signing game. The comparison event is stated literally as validity and raw same-key message freshness, rather than as a protocol authentication conclusion. Actual native stopping receipts supply that event separately. Failed selected generation gives false on both sides. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeReduction
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaEuf (PublicKey Forgery Valid Fresh)
open RegistrationNativeMldsaCandidate (requestsFor)
open RegistrationNativeMldsaChosenProgram (interpreted)
variable (source : Source)

noncomputable def adversary {count : Nat} (target : Fin (count + 1))
    (work : PublicKey → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery))
    (publicKey : PublicKey) : OracleComp RegistrationNativeMldsaEuf.Spec (Option Forgery) := do
  let others ← RegistrationNativeMldsaChosen.lift (RegistrationNativeMldsaEager.family source count)
  let result ← RegistrationNativeMldsaEufTape.evaluate source publicKey
    (RegistrationNativeMldsaEufTape.selectedTape source target others) (work publicKey) {}
  pure result.1

def RawWin (publicKey : PublicKey) (result : Option Forgery × RegistrationNativeMldsaOpaque.Pool source) : Prop :=
  ∃ forgery, result.1 = some forgery ∧ Valid source publicKey forgery ∧ Fresh (requestsFor publicKey result.2.signing) forgery

noncomputable def sourceGame {count : Nat} (target : Fin (count + 1))
    (work : PublicKey → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery)) : ProbComp Bool := do
  match ← RegistrationNativeMldsa.generate source with
  | none => pure false
  | some challenge => do
      let others ← RegistrationNativeMldsaEager.family source count
      let result ← (simulateQ (RegistrationNativeMldsaEager.handler source
        (List.ofFn (target.insertNth (some challenge) others))) (work challenge.publicKey)).run {}
      pure (@decide (RawWin source challenge.publicKey result) (Classical.propDecidable _))

private theorem fixed (challenge : Credential source) {count : Nat} (target : Fin (count + 1))
    (others : Fin count → Option (Credential source))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery)) :
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source
      (List.ofFn (target.insertNth (some challenge) others))) work).run {}}[RawWin source challenge.publicKey result] ≤
    Pr{let result ← interpreted source challenge (RegistrationNativeMldsaEufTape.evaluate source challenge.publicKey
      (RegistrationNativeMldsaEufTape.selectedTape source target others) work {}) []}[
      ∃ forgery, result.1.1 = some forgery ∧ Valid source challenge.publicKey forgery ∧ Fresh result.2 forgery] := by
  rw [← RegistrationNativeMldsaEufTape.selected_program source challenge target others work [], prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun result supported accepted => by
    obtain ⟨forgery, selected, valid, fresh⟩ := accepted
    refine ⟨forgery, selected, valid, ?_⟩
    exact RegistrationNativeMldsaEufTapeHistory.fresh source challenge
      (RegistrationNativeMldsaEufTape.selectedTape source target others) work {} []
      (by intro request impossible; cases impossible) result supported forgery fresh

private theorem game_expanded {count : Nat} (target : Fin (count + 1))
    (work : PublicKey → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery)) :
    RegistrationNativeMldsaEuf.game source (adversary source target work) = (do
      match ← RegistrationNativeMldsa.generate source with
      | none => pure false
      | some challenge => do
          let others ← RegistrationNativeMldsaEager.family source count
          let result ← interpreted source challenge (RegistrationNativeMldsaEufTape.evaluate source challenge.publicKey
            (RegistrationNativeMldsaEufTape.selectedTape source target others) (work challenge.publicKey) {}) []
          pure (@decide (∃ forgery, result.1.1 = some forgery ∧ Valid source challenge.publicKey forgery ∧ Fresh result.2 forgery)
            (Classical.propDecidable _))) := by
  unfold RegistrationNativeMldsaEuf.game
  apply bind_congr
  intro generated
  cases generated with
  | none => rfl
  | some challenge =>
      simp only [adversary, simulateQ_bind, StateT.run_bind, simulateQ_pure,
        StateT.run_pure, pure_bind, bind_assoc]
      change (interpreted source challenge
        (RegistrationNativeMldsaChosen.lift (RegistrationNativeMldsaEager.family source count)) [] >>= fun others => _) = _
      rw [RegistrationNativeMldsaChosenProgram.ordinary, bind_map_left]
      rfl

/-- The executable reduction gives an ordinary generated-key EUF upper bound with no source-security or authentication premise. -/
theorem bound {count : Nat} (target : Fin (count + 1))
    (work : PublicKey → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery)) :
    Pr{let won ← sourceGame source target work}[won = true] ≤
      RegistrationNativeMldsaEuf.advantage source (adversary source target work) := by
  classical
  rw [RegistrationNativeMldsaEuf.advantage, ← prEvent_eq_evalDist_singleton _ true, game_expanded]
  unfold sourceGame
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun generated _ => ?_
  cases generated with
  | none => rfl
  | some challenge =>
      refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun others _ => ?_
      rw [bind_pure_comp, bind_pure_comp, prEvent_map, prEvent_map]
      simpa only [decide_eq_true_eq] using fixed source challenge target others (work challenge.publicKey)
end BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeReduction

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeReduction.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeReduction.bound
