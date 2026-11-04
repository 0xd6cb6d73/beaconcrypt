-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCodecControlNormalization

/-! The selected public preflight callsites supply exactly six literal field tags. Unrolling their finite traversal retains the state passed to each next step and every monadic early exit. This lemma says nothing about unbounded or dynamically supplied field lists. -/
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationCodecFixedFields
universe u v w
variable {A : Type u} {S : Type v} {m : Type v → Type w} [Monad m] [LawfulMonad m]

theorem fold_six (step : S → A → m S) (initial : S) (a b c d e f : A) :
    [a,b,c,d,e,f].foldlM step initial = (do
      let first ← step initial a
      let second ← step first b
      let third ← step second c
      let fourth ← step third d
      let fifth ← step fourth e
      step fifth f) := by
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]

end BeaconcryptCore.Refinement.RegistrationCodecFixedFields

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecFixedFields.fold_six' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecFixedFields.fold_six
