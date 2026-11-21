-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.LazyOracleDiscard
import BeaconcryptCore.Computational.PqxdhFullSecretInputKdf

/-! A single private child response may be drawn on its first actual use or before the complete adaptive program. The optional cell records whether it was used; no equality of marginal distributions substitutes for the complete continuation law. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftDeferredChild
open PqxdhFullSecretInputKdf LazyOracleDiscard

abbrev Spec := (Unit →ₒ FullOutput) + unifSpec

/-- One persistent private child, with every other random request forwarded literally. -/
noncomputable def lazyImpl (draw : ProbComp FullOutput) : QueryImpl Spec (StateT (Option FullOutput) ProbComp)
  | .inl _ => fun state => match state with
      | some value => pure (value, state)
      | none => (fun value => (value, some value)) <$> draw
  | .inr query => fun state => (fun value => (value, state)) <$> unifSpec.query query

/-- The supplied child is installed only when requested; an unused pre-sample never appears in the final cell. -/
def supplied (value : FullOutput) : QueryImpl Spec (StateT (Option FullOutput) ProbComp)
  | .inl _ => fun _ => pure (value, some value)
  | .inr query => fun state => (fun reply => (reply, state)) <$> unifSpec.query query

/-- Once installed, the supplied child and the original lazy child agree through every adaptive continuation. -/
theorem filled {Result : Type} (draw : ProbComp FullOutput) (value : FullOutput)
    (client : OracleComp Spec Result) :
    (simulateQ (lazyImpl draw) client).run (some value) =
      (simulateQ (supplied value) client).run (some value) := by
  induction client using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind query next ih =>
      rcases query with request | query <;>
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lazyImpl, supplied]
      all_goals simp only [StateT.run, pure_bind, bind_map_left]
      · exact ih value
      · exact bind_congr ih

/-- Moving the child draw to the front preserves the complete evaluated adaptive program and optional final cell under every continuation, including executions that never request it. -/
theorem initial_law {Result : Type} (draw : ProbComp FullOutput) (client : OracleComp Spec Result) :
    LawEq ((simulateQ (lazyImpl draw) client).run none)
      (draw >>= fun value => (simulateQ (supplied value) client).run none) := by
  induction client using OracleComp.inductionOn with
  | pure result =>
      simpa only [simulateQ_pure, StateT.run_pure] using
        (lawEq_drop draw (pure (result, (none : Option FullOutput)))).symm
  | query_bind query next ih =>
      rcases query with request | query <;>
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lazyImpl, supplied]
      all_goals simp only [StateT.run, pure_bind, bind_map_left]
      · exact (LawEq.refl draw).bind (fun value => LawEq.of_eq (filled draw value (next value)))
      · exact ((LawEq.refl (unifSpec.query query)).bind ih).trans
          (lawEq_swap (unifSpec.query query) draw
            (fun reply value => (simulateQ (supplied value) (next reply)).run none))

end BeaconcryptCore.Computational.PqxdhRecordLiftDeferredChild

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftDeferredChild.filled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftDeferredChild.filled

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftDeferredChild.initial_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftDeferredChild.initial_law
