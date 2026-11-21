-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecipientFailure

/-! An exact private sticky primitive-failure marker preserves the original adaptive value/state distribution. A syntactic count of the actual charged requests gives its union bound from individual primitive response laws, retaining all adaptive continuations. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
namespace BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound
variable {κ S V : Type} {spec : OracleSpec κ}

noncomputable def handler (implementation : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → spec.Range query → Prop) : QueryImpl spec (StateT (S × Bool) ProbComp) :=
  fun query before => (fun result => (result.1, (result.2, before.2 || @decide (bad query result.1) (Classical.propDecidable _)))) <$>
    (implementation query).run before.1

/-- Forgetting only the private failure marker retains the complete original adaptive source execution. -/
theorem erase (implementation : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → spec.Range query → Prop) (work : OracleComp spec V) (before : S × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (handler implementation bad) work).run before =
      (simulateQ implementation work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [handler, StateT.run, Functor.map_map, Prod.map, id_eq]
  exact id_map _

/-- A genuine syntactic request cap and per-response primitive failure law bound the actual final sticky marker, without a protocol-event or source-game equivalence premise. -/
theorem bound (implementation : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → spec.Range query → Prop) (charged : spec.Domain → Prop) [DecidablePred charged]
    (delta : ENNReal)
    (step : ∀ query before, Pr{let result ← (implementation query).run before}[bad query result.1] ≤ if charged query then delta else 0)
    (work : OracleComp spec V) (cap : Nat) (bounded : work.IsQueryBoundP charged cap) (before : S) :
    Pr{let result ← (simulateQ (handler implementation bad) work).run (before, false)}[result.2.2 = true] ≤ cap * delta := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, Bool.false_eq_true, ite_false, zero_le]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    obtain ⟨room, rest⟩ := bounded
    rw [simulateQ_query_bind, StateT.run_bind]
    have tail : ∀ result : spec.Range query × (S × Bool), ¬ result.2.2 = true →
        Pr{let outcome ← (simulateQ (handler implementation bad) (next result.1)).run result.2}[outcome.2.2 = true] ≤
          (if charged query then cap - 1 else cap) * delta := by
      intro result clean
      rcases result with ⟨reply, after, flag⟩
      cases flag with
      | true => exact False.elim (clean rfl)
      | false => exact ih reply _ (rest reply) after
    have union := prEvent_bind_le_prEvent_add ((handler implementation bad query).run (before, false))
      (fun result => (simulateQ (handler implementation bad) (next result.1)).run result.2)
      (fun result => result.2.2 = true) (fun result => result.2.2 = true) tail
    have first : Pr{let result ← (handler implementation bad query).run (before, false)}[result.2.2 = true] ≤
        if charged query then delta else 0 := by
      simpa only [handler, StateT.run, prEvent_map, Bool.false_or, decide_eq_true_eq] using step query before
    calc
      _ ≤ Pr{let result ← (handler implementation bad query).run (before, false)}[result.2.2 = true] +
          (if charged query then cap - 1 else cap) * delta := union
      _ ≤ (if charged query then delta else 0) + (if charged query then cap - 1 else cap) * delta := add_le_add first le_rfl
      _ = cap * delta := by
        by_cases counted : charged query
        · have positive : 0 < cap := room.resolve_left (not_not_intro counted)
          have capEq : cap = 1 + (cap - 1) := by omega
          simp only [counted, ite_true]
          conv_rhs => rw [capEq]
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        · simp only [counted, ite_false, zero_add]

end BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound.bound
