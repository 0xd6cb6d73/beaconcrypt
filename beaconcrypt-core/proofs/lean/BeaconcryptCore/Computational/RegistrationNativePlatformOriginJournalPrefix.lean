-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
/-! Every private chronological journal retains its literal past and each same callback reply under arbitrary adaptive later work. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix
open RegistrationNativeStageTrace (Call)
variable {Q R S View A : Type} {spec : OracleSpec Q} {target : OracleSpec R}
variable (observe : S → View) (implementation : QueryImpl spec (StateT S (OracleComp target)))

/-- Arbitrary adaptive later work only appends to the same original observed journal. -/
theorem append_only (work : OracleComp spec A) (before : S × List (Call spec View))
    (result : A × (S × List (Call spec View)))
    (supported : result∈support ((simulateQ (RegistrationNativeObservedStageTrace.handler observe implementation) work).run before)) :
    ∃added,result.2.2=before.2++added := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨[],(List.append_nil _).symm⟩
  | query_bind query next ih=>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,later⟩ := supported
    simp only [RegistrationNativeObservedStageTrace.handler,StateT.run,support_map] at called
    obtain ⟨actual,_reached,rfl⟩ := called
    obtain ⟨added,recorded⟩ := ih actual.1 (actual.2,before.2++[⟨query,observe before.1,actual.1,observe actual.2⟩]) result later
    exact ⟨⟨query,observe before.1,actual.1,observe actual.2⟩::added,by simpa only [List.append_assoc,List.singleton_append] using recorded⟩

/-- A prior recorded call stays at its original chronological index after arbitrary later source work. -/
theorem prior (work : OracleComp spec A) (before : S × List (Call spec View))
    (result : A × (S × List (Call spec View))) (index : Nat) (call : Call spec View)
    (recorded : before.2[index]?=some call)
    (supported : result∈support ((simulateQ (RegistrationNativeObservedStageTrace.handler observe implementation) work).run before)) :
    result.2.2[index]?=some call := by
  obtain ⟨added,appended⟩ := append_only observe implementation work before result supported
  have bounded : index<before.2.length := by
    by_contra late
    have absent : before.2[index]?=none := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt late)
    rw [recorded] at absent
    cases absent
  rw [appended,List.getElem?_append_left bounded]
  exact recorded

/-- The same actual current callback and reply are fixed at the original journal length throughout its adaptive original suffix. -/
theorem current (query : spec.Domain) (next : spec.Range query → OracleComp spec A)
    (before : S × List (Call spec View)) (result : A × (S × List (Call spec View)))
    (supported : result∈support ((simulateQ (RegistrationNativeObservedStageTrace.handler observe implementation) (spec.query query >>=next)).run before)) :
    ∃actual∈support ((implementation query).run before.1),
      result.2.2[before.2.length]?=some ⟨query,observe before.1,actual.1,observe actual.2⟩ := by
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,later⟩ := supported
  simp only [RegistrationNativeObservedStageTrace.handler,StateT.run,support_map] at called
  obtain ⟨actual,reached,rfl⟩ := called
  refine ⟨actual,reached,prior observe implementation (next actual.1)
    (actual.2,before.2++[⟨query,observe before.1,actual.1,observe actual.2⟩]) result before.2.length _ ?_ later⟩
  simp only [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix.append_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix.append_only
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix.prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix.prior
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix.current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalPrefix.current
