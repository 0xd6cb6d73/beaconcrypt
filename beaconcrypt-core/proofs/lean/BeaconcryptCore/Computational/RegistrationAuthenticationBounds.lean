-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationCompiler

/-! Structural resource bounds for the actual native authentication executor, including every failed getter and rejected continuation. The conservative entry-point bill counts five fuel steps; the separate acceptance theorem still derives the exact four actual callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationAuthenticationBounds
open RegistrationAuthenticationExecutor
open PqxdhRecordLiftInterface (EffectKind effectKind)
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)
variable {Input Result : Type} {n : Nat}

private theorem continue_bound (value : RustM Input) (next : Input → OracleComp Spec (RustM Result))
    (cap : Nat) (bounded : ∀ input, (next input).IsTotalQueryBound cap) :
    (continueWith value next).IsTotalQueryBound cap := by
  cases value with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

/-- Each actual controller step either terminates or makes exactly one callback. -/
theorem step_bound (state : registration.InitAuthentication) : (step state).IsTotalQueryBound 1 := by
  cases state <;> simp only [step]
  all_goals first
    | trivial
    | apply continue_bound
      intro request
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => by trivial⟩

/-- Fuel bounds the actual source callbacks on every reply path, including error and divergence. -/
theorem execute_bound (fuel : Nat) (state : registration.InitAuthentication) :
    (execute fuel state).IsTotalQueryBound fuel := by
  induction fuel generalizing state with
  | zero => trivial
  | succ fuel ih =>
      rw [execute]
      have tail : ∀ (result : RustM (Option (Event × registration.InitAuthentication))),
          (continueWith result fun next => match next with
          | none => pure (.ok ([], state))
          | some (event, after) => do
              let rest ← execute fuel after
              continueWith rest fun final => pure (.ok (event :: final.1, final.2))).IsTotalQueryBound fuel := by
        intro result
        apply continue_bound
        intro next
        cases next with
        | none => trivial
        | some next =>
            have finished : ∀ (result : RustM (List Event × registration.InitAuthentication)), (continueWith result fun final =>
                pure (.ok (next.1 :: final.1, final.2))).IsTotalQueryBound 0 := by
              intro result
              exact continue_bound result _ 0 (fun _ => by trivial)
            simpa only [Nat.add_zero] using isTotalQueryBound_bind (ih next.2) finished
      have combined := isTotalQueryBound_bind (step_bound state) tail
      rw [Nat.add_comm 1 fuel] at combined
      convert combined using 1

attribute [local irreducible] execute registration.begin_init_authentication

/-- Native Init authentication never exceeds its actual five-step source executor. -/
theorem begin_bound (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    (begin pin packet).IsTotalQueryBound 5 :=
  continue_bound (registration.begin_init_authentication pin packet) _ 5 (execute_bound 5)

/-- The compiled entry point has at most five shared-cache hash calls and no explicit coin or administrative call. -/
theorem program_bound (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (kind : EffectKind) :
    (RegistrationAuthenticationCompiler.program (n := n) crypto verify pin packet).IsQueryBoundP
      (fun query => effectKind query = kind) (if kind = .hash then 5 else 0) := by
  unfold RegistrationAuthenticationCompiler.program
  by_cases selected : kind = .hash
  · subst kind
    simp only [ite_true]
    apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ _ 5
      ((isQueryBoundP_true_iff _ _).mpr (begin_bound pin packet))
    intro query
    simpa only [ite_true] using RegistrationAuthenticationCompiler.callback_bound (n := n) crypto verify query .hash
  · rw [ite_eq_right selected]
    apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro query
    simpa only [ite_eq_right selected, ite_false] using
      RegistrationAuthenticationCompiler.callback_bound (n := n) crypto verify query kind

end BeaconcryptCore.Computational.RegistrationAuthenticationBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationBounds.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationBounds.step_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationBounds.execute_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationBounds.execute_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationBounds.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationBounds.begin_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationBounds.program_bound
