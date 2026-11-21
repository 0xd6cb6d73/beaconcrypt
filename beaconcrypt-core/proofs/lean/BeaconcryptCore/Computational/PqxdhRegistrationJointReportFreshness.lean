-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource
import BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedRevealSchedule

/-! Report-time freshness is the absence of an actual successful native seed disclosure at the routed source index. The proof derives the ordinary public history from the same complete initialized execution, including rejected requests and later compromise. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhDynamicIdentityReports
open PqxdhJointIdentityFreshness PqxdhDynamicIdentityRouting
open PqxdhRegistrationJointRoutedReveals (revealAt revealedAt Recorded)
open PqxdhRegistrationJointIdentityRouting (Registry route)
open PqxdhRegistrationJointReportLift (Spec extend erase)

/-- Only an actual successful reveal reply adds the corresponding generated index to the ordinary freshness history. -/
theorem history_step {count : Nat} (target : Fin count) (request : DynamicSpec.Domain)
    (answer : DynamicSpec.Range request) (history : GlobalState count) :
    target ∈ (historyUpdate count request answer history).reveals ↔
      target ∈ history.reveals ∨ revealAt target.val ⟨request, answer⟩ = true := by
  rcases request with coin | request
  case inl => simp [historyUpdate, revealAt]
  case inr =>
    cases request
    case create => simp [historyUpdate, revealAt]
    case service index request =>
      by_cases valid : index < count <;> cases request <;> cases answer <;>
        simp [historyUpdate, valid, PqxdhJointIdentityEvents.publicUpdate, revealAt]
    case reveal index =>
      by_cases valid : index < count
      · cases answer <;> simp [historyUpdate, valid, PqxdhJointIdentityEvents.publicUpdate, revealAt, Fin.ext_iff]
        exact or_congr Iff.rfl eq_comm
      · have different : index ≠ target.val := fun equal => valid (equal ▸ target.isLt)
        cases answer <;> simp [historyUpdate, valid, revealAt, different]

/-- The ordinary history and actual chronological reply audit agree after every source query. -/
theorem source_step (joint : Primitives) {count : Nat} (target : Fin count)
    (request : DynamicSpec.Domain) (state : GlobalState count × SourceState)
    (result : DynamicSpec.Range request × (GlobalState count × SourceState))
    (before : target ∈ state.1.reveals ↔ revealedAt target.val state.2.transcript = true)
    (supported : result ∈ support ((sourceWithHistory count (lazyImpl joint) request).run state)) :
    target ∈ result.2.1.reveals ↔ revealedAt target.val result.2.2.transcript = true := by
  rw [sourceWithHistory_run] at supported
  obtain ⟨reply, member, returned⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ returned
  simp [history_step, before, lazyImpl_transcript joint request state.2 reply member, revealedAt]

/-- Reports themselves disclose nothing; ordinary services update freshness using their actual optional answer. -/
theorem reporting_query (joint : Primitives) (count : Nat) (request : ReportingSpec.Domain)
    (state : ReportingState count)
    (before : ∀ target : Fin count, target ∈ state.source.1.reveals ↔
      revealedAt target.val state.source.2.transcript = true)
    (result : ReportingSpec.Range request × ReportingState count)
    (supported : result ∈ support ((reportingImpl joint count request).run state)) :
    ∀ target : Fin count, target ∈ result.2.source.1.reveals ↔
      revealedAt target.val result.2.source.2.transcript = true := by
  cases request with
  | inr report =>
      obtain rfl := eq_of_mem_support_pure supported
      exact before
  | inl request =>
      simp only [reportingImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, actual, returned⟩ := supported
      obtain rfl := eq_of_mem_support_pure returned
      exact fun target => source_step joint target request state.source answer (before target) actual

/-- The complete linked source/report callback preserves the actual successful-reveal audit. -/
theorem source_query (joint : Primitives) (count : Nat)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain)
    (state : PqxdhJointPhase1Reports.Monitor count × ReportingState count)
    (before : ∀ target : Fin count, target ∈ state.2.source.1.reveals ↔
      revealedAt target.val state.2.source.2.transcript = true)
    (result : PqxdhJointPhase1Reports.ProtocolSpec.Range request ×
      (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count request).run state)) :
    ∀ target : Fin count, target ∈ result.2.2.source.1.reveals ↔
      revealedAt target.val result.2.2.source.2.transcript = true := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, actual, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact OracleComp.simulateQ_run_preservesInv (reportingImpl joint count)
    (fun state => ∀ target : Fin count, target ∈ state.source.1.reveals ↔
      revealedAt target.val state.source.2.transcript = true)
    (fun request state before result member => reporting_query joint count request state before result member)
    _ state.2 before inner actual

/-- Every actual report-game prefix has exactly the successful source reveals in its public freshness snapshot. -/
theorem snapshot {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp PqxdhJointPhase1Reports.ProtocolSpec Result)
    (result : Result × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count work)) :
    ∀ target : Fin count, target ∈ result.2.1.snapshot.history.reveals ↔
      revealedAt target.val result.2.2.source.2.transcript = true := by
  have actual := OracleComp.simulateQ_run_preservesInv (PqxdhJointPhase1Reports.sourceImpl joint count)
    (fun state => ∀ target : Fin count, target ∈ state.2.source.1.reveals ↔
      revealedAt target.val state.2.source.2.transcript = true)
    (fun request state before result member => source_query joint count request state before result member)
    work (PqxdhJointPhase1Reports.initialMonitor count, ⟨initialSource count, initialSnapshot count, false, []⟩)
    (by simp [initialSource, PqxdhJointIdentityFreshness.initialState, PqxdhDynamicIdentityPool.initialState, revealedAt])
    result supported
  rw [(PqxdhRegistrationJointRoutedReportHistory.snapshot joint count work result supported).1]
  exact actual

/-- The source-to-generated successful disclosure relation is derived for the actual report-bearing schedule from its empty initial states. -/
theorem recorded {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp (Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (result : (Result × Registry) × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count
      ((simulateQ (extend (route joint)) work).run ⟨[], []⟩))) :
    Recorded (result.1.2, result.2.2.source.2) := by
  have actual : (result.1.1, (result.1.2, result.2.2.source.2)) ∈ support
      ((fun result => (result.1.1, (result.1.2, result.2.2.source.2))) <$>
        PqxdhJointPhase1Reports.run joint count
          ((simulateQ (extend (route joint)) work).run ⟨[], []⟩)) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  unfold PqxdhJointPhase1Reports.run at actual
  rw [PqxdhRegistrationJointRoutedReportSource.projection] at actual
  exact PqxdhRegistrationJointRoutedRevealSchedule.program joint (simulateQ erase work)
    _ PqxdhRegistrationJointRoutedHistory.initial PqxdhRegistrationJointRoutedReveals.initial _ actual

/-- Report-time generated freshness is exactly the absence of a successful native seed disclosure at the corresponding source handle. -/
theorem fresh {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp (Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (result : (Result × Registry) × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count
      ((simulateQ (extend (route joint)) work).run ⟨[], []⟩)))
    (index : Nat) (target : Fin count)
    (found : result.1.2.refs[index]? = some (.generated target.val)) :
    target ∉ result.2.1.snapshot.history.reveals ↔ revealedAt index result.1.2.transcript = false := by
  rw [snapshot joint count _ result supported target,
    ← (recorded joint count work result supported).generated index target.val found]
  simp

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.history_step' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.history_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.source_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.reporting_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.reporting_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.source_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.snapshot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness.fresh
