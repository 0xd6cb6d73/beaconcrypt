-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-! The sticky recipient marker covers every bad request/reply in the literal capability log of that same adaptive execution. The original implementation state and every reply are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
namespace BeaconcryptCore.Computational.RegistrationNativeRecipientLog
variable {ι State Value : Type} {spec : OracleSpec ι}

private theorem query_bind_log (query : spec.Domain) (next : spec.Range query → OracleComp spec Value) :
    OracleComp.withQueryLog (((spec.query query : OracleComp spec _) >>= next) : OracleComp spec Value) = (do
      let reply ← (spec.query query : OracleComp spec _)
      (fun result => (result.1, ⟨query, reply⟩ :: result.2)) <$> (next reply).withQueryLog) := by
  rw [withQueryLog_bind, withQueryLog_query]
  simp only [bind_assoc, pure_bind]
  rfl

/-- A previously set marker stays set, and every bad actual logged reply sets the final marker. -/
theorem sound (implementation : QueryImpl spec (StateT State ProbComp))
    (bad : (query : spec.Domain) → spec.Range query → Prop)
    (work : OracleComp spec Value) (before : State × Bool)
    (value : Value) (log : spec.QueryLog) (after : State × Bool)
    (supported : ((value, log), after) ∈ support
      ((simulateQ (RegistrationNativeRecipientQueryBound.handler implementation bad) work.withQueryLog).run before)) :
    (before.2 = true → after.2 = true) ∧
      (∀ entry ∈ log, bad entry.1 entry.2 → after.2 = true) := by
  induction work using OracleComp.inductionOn generalizing before value log after with
  | pure returned =>
    simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rcases supported with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨id, fun _ member => False.elim (List.not_mem_nil member)⟩
  | query_bind query next ih =>
    rw [query_bind_log, simulateQ_bind, StateT.run_bind] at supported
    simp only [simulateQ_spec_query, mem_support_bind_iff] at supported
    obtain ⟨⟨reply, middle⟩, head, tail⟩ := supported
    simp only [RegistrationNativeRecipientQueryBound.handler, StateT.run, support_map] at head
    obtain ⟨⟨actual, actualState⟩, _, same⟩ := head
    cases same
    rw [simulateQ_map, StateT.run_map, support_map] at tail
    obtain ⟨⟨⟨tailValue, tailLog⟩, afterState⟩, tailRun, returned⟩ := tail
    simp only [Prod.mk.injEq] at returned
    rcases returned with ⟨⟨rfl, rfl⟩, rfl⟩
    have rest := ih actual (actualState, before.2 || @decide (bad query actual) (Classical.propDecidable _))
      tailValue tailLog afterState tailRun
    refine ⟨fun prior => rest.1 ?_, ?_⟩
    · simp only [prior, Bool.true_or]
    · intro entry member invalid
      rcases List.mem_cons.mp member with same | later
      · cases same
        apply rest.1
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr invalid
      · exact rest.2 entry later invalid

end BeaconcryptCore.Computational.RegistrationNativeRecipientLog

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientLog.sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientLog.sound
