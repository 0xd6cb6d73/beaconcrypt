-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-! A private higher request/reply trace is related to the literal lower capability log of the same macro execution. Successful higher replies inherit facts from their own executed lower block, with prefix and suffix effects retained. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationAgreementMacroTrace
open RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace
variable {ι State Value : Type} {lower : OracleSpec ι}

/-- Each retained higher entry is either an initial entry or satisfies the reached block's monotone lower-log receipt. -/
theorem program (implementation : QueryImpl Spec (StateT State (OracleComp lower)))
    (relation : Entry → lower.QueryLog → Prop)
    (left : ∀ entry first second, relation entry first → relation entry (first ++ second))
    (right : ∀ entry first second, relation entry second → relation entry (first ++ second))
    (step : ∀ query before reply after log,
      ((reply, after), log) ∈ support ((implementation query).run before).withQueryLog →
      relation ⟨query, reply⟩ log)
    (work : OracleComp Spec Value) (journal final : Trace) (before after : State) (value : Value)
    (log : lower.QueryLog)
    (supported : (((value, final), after), log) ∈ support
      ((simulateQ implementation (trace work journal)).run before).withQueryLog) :
    ∀ entry ∈ final, entry ∈ journal ∨ relation entry log := by
  induction work using OracleComp.inductionOn generalizing journal final before after value log with
  | pure returned =>
    simp only [trace_pure, simulateQ_pure, StateT.run_pure, withQueryLog_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rcases supported with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    exact fun entry member => Or.inl member
  | query_bind query next ih =>
    rw [trace_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, withQueryLog_bind] at supported
    simp only [mem_support_bind_iff, support_map] at supported
    obtain ⟨⟨⟨reply, middle⟩, prefixLog⟩, head, ⟨suffix, suffixLog⟩, tail, returned⟩ := supported
    simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
    rcases returned with ⟨sameValue, sameLog⟩
    cases sameValue
    cases sameLog
    intro entry member
    have receipt := ih reply (journal ++ [⟨query, reply⟩]) final middle after value suffixLog tail entry member
    rcases receipt with old | current
    · rcases List.mem_append.mp old with initial | recent
      · exact Or.inl initial
      · have named : entry = ⟨query, reply⟩ := List.mem_singleton.mp recent
        subst entry
        exact Or.inr (left _ _ _ (step query before reply middle prefixLog head))
    · exact Or.inr (right _ _ _ current)

/-- Mapping a returned analysis value keeps the complete lower query/reply log. -/
theorem logging_map {Output : Type} (function : Value → Output) (work : OracleComp lower Value) :
    (function <$> work).withQueryLog = Prod.map function id <$> work.withQueryLog := by
  rw [map_eq_bind_pure_comp, withQueryLog_bind]
  simp only [Function.comp_apply, withQueryLog_pure, map_pure, Prod.map, id_eq, List.append_nil, bind_pure_comp]
  rfl

/-- Adding the private higher trace lifts any reached result without changing its exact lower capability log or final state. -/
theorem lift_support (implementation : QueryImpl Spec (StateT State (OracleComp lower)))
    (work : OracleComp Spec Value) (before after : State) (value : Value) (log : lower.QueryLog)
    (supported : ((value, after), log) ∈ support ((simulateQ implementation work).run before).withQueryLog) :
    ∃ journal, (((value, journal), after), log) ∈ support
      ((simulateQ implementation (trace work [])).run before).withQueryLog := by
  let erase : (Value × Trace) × State → Value × State := fun result => (result.1.1, result.2)
  have erasure : erase <$> (simulateQ implementation (trace work [])).run before =
      (simulateQ implementation work).run before := by
    have same := congrArg (fun program => (simulateQ implementation program).run before)
      (RegistrationAgreementQueryTrace.erasure work [])
    simpa only [simulateQ_map, StateT.run_map] using same
  have logged : Prod.map erase id <$>
      ((simulateQ implementation (trace work [])).run before).withQueryLog =
      ((simulateQ implementation work).run before).withQueryLog := by
    rw [← logging_map, erasure]
  rw [← logged, support_map] at supported
  obtain ⟨⟨⟨⟨returned, journal⟩, finalState⟩, finalLog⟩, reached, same⟩ := supported
  simp only [Prod.map, erase, id_eq, Prod.mk.injEq] at same
  rcases same with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨journal, reached⟩

end BeaconcryptCore.Computational.RegistrationAgreementMacroTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementMacroTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementMacroTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementMacroTrace.logging_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementMacroTrace.logging_map

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementMacroTrace.lift_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementMacroTrace.lift_support
