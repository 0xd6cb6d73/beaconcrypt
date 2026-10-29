-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport

/-! The ordinary report interpreter's public snapshot is the exact replay of the actual indexed source transcript. Source key creation, signing, optional DH and reveals retain their chronological replies. The correspondence is initialized and preserved operationally, without a caller-supplied monitor history. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot
open PqxdhDynamicIdentityPool (DynamicSpec Observation SourceState lazyImpl)
open PqxdhDynamicIdentityReports (ReportingSpec ReportingState reportingImpl sourceSnapshot)
open PqxdhJointIdentityFreshness (GlobalState)
open RegistrationNativeIdentityHistory (replay)

def ReportingConsistent (joint : PqxdhJointIdentity.Primitives) {count : Nat} (before : ReportingState count) : Prop :=
  before.publicSnapshot = sourceSnapshot joint before.source ∧
    before.source.1 = replay count before.source.2.transcript

theorem replay_append (count : Nat) (transcript : List Observation) (observation : Observation) :
    replay count (transcript ++ [observation]) =
      PqxdhDynamicIdentityRouting.historyUpdate count observation.1 observation.2 (replay count transcript) := by
  simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem history_step (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : DynamicSpec.Domain)
    (before : GlobalState count × SourceState) (result : DynamicSpec.Range query × (GlobalState count × SourceState))
    (prior : before.1 = replay count before.2.transcript)
    (supported : result ∈ support ((PqxdhDynamicIdentityRouting.sourceWithHistory count (lazyImpl joint) query).run before)) :
    result.2.1 = replay count result.2.2.transcript := by
  rw [PqxdhDynamicIdentityRouting.sourceWithHistory_run] at supported
  obtain ⟨reply, reached, finished⟩ := (mem_support_bind_iff _ _ _).mp supported
  simp only [mem_support_pure_iff] at finished
  cases finished
  rw [PqxdhDynamicIdentityPool.lazyImpl_transcript joint query before.2 reply reached, replay_append, ← prior]

/-- Every actual report-interpreter query retains its exact source snapshot and replayed chronological history. -/
theorem reporting_step (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : ReportingSpec.Domain)
    (before : ReportingState count) (result : ReportingSpec.Range query × ReportingState count)
    (prior : ReportingConsistent joint before)
    (supported : result ∈ support ((reportingImpl joint count query).run before)) :
    ReportingConsistent joint result.2 := by
  cases query with
  | inl request =>
      simp only [reportingImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨response, reached, finished⟩ := supported
      simp only [mem_support_pure_iff] at finished
      cases finished
      refine ⟨?_, history_step joint count request before.source response prior.2 reached⟩
      change PqxdhDynamicIdentityReports.observe request response.1 before.publicSnapshot = sourceSnapshot joint response.2
      rw [prior.1, PqxdhDynamicIdentityReports.source_snapshot_step joint count request before.source response reached]
  | inr candidate =>
      simp only [reportingImpl, StateT.run, mem_support_pure_iff] at supported
      cases supported
      exact prior

/-- Empty source initialization determines the report interpreter's complete public and chronological state. -/
theorem reporting_initial (joint : PqxdhJointIdentity.Primitives) (count : Nat) :
    ReportingConsistent joint
      (⟨PqxdhDynamicIdentityReports.initialSource count, PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩ : ReportingState count) :=
  ⟨rfl, rfl⟩

/-- The source-facing snapshot is exactly the one used in the native prekey-or-report adapter. -/
theorem reporting_snapshot (joint : PqxdhJointIdentity.Primitives) {count : Nat} (before : ReportingState count)
    (consistent : ReportingConsistent joint before) :
    before.publicSnapshot = RegistrationNativeIdentityHistoryReport.snapshot joint count before.source.2 := by
  rw [consistent.1]
  simp only [sourceSnapshot, RegistrationNativeIdentityHistoryReport.snapshot, consistent.2]

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.replay_append' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.replay_append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.history_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.reporting_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.reporting_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.reporting_initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.reporting_initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.reporting_snapshot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot.reporting_snapshot
