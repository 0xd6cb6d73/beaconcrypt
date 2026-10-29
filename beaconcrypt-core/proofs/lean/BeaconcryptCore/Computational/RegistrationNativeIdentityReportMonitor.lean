-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportSnapshot

/-! The ordinary joint field-origin monitor computes the exact snapshot reconstructed from the actual private source transcript at every reached adaptive prefix. Initialization and every monitor transition establish this fact; no caller supplies a desired monitor/source correspondence. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor
open PqxdhJointPhase1Reports (ProtocolSpec Monitor)
open PqxdhDynamicIdentityReports (ReportingState)
open RegistrationNativeIdentityReportSnapshot (ReportingConsistent)
variable {Value : Type}

abbrev State (count : Nat) := Monitor count × ReportingState count

def Consistent (joint : PqxdhJointIdentity.Primitives) {count : Nat} (before : State count) : Prop :=
  PqxdhJointPhase1Reports.Compatible before.1 before.2 ∧ ReportingConsistent joint before.2

def initial (count : Nat) : State count :=
  (PqxdhJointPhase1Reports.initialMonitor count,
    ⟨PqxdhDynamicIdentityReports.initialSource count, PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩)

/-- Every actual ordinary monitor callback keeps the native snapshot and complete source history aligned. -/
theorem query_consistent (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : ProtocolSpec.Domain)
    (before : State count) (result : ProtocolSpec.Range query × State count) (prior : Consistent joint before)
    (supported : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count query).run before)) :
    Consistent joint result.2 := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, reached, returned⟩ := OracleComp.mem_support_map_peel _ _ supported
  cases returned
  have compatible := PqxdhJointPhase1Reports.wrapper_source_preserves joint count query before.1 before.2 prior.1 inner reached
  have retained := OracleComp.simulateQ_run_preserves_inv_of_query
    (PqxdhDynamicIdentityReports.reportingImpl joint count) (ReportingConsistent joint)
    (fun query current valid next actual => RegistrationNativeIdentityReportSnapshot.reporting_step joint count query current next valid actual)
    ((PqxdhJointPhase1Reports.wrapper joint count query).run before.1) before.2 prior.2 inner reached
  exact ⟨compatible, retained⟩

/-- Literal empty initialization determines the complete ordinary monitor/source relation. -/
theorem initial_consistent (joint : PqxdhJointIdentity.Primitives) (count : Nat) : Consistent joint (initial count) :=
  ⟨⟨rfl, rfl⟩, RegistrationNativeIdentityReportSnapshot.reporting_initial joint count⟩

/-- Every reached adaptive prefix retains the same literal snapshot and per-handle signing history. -/
theorem program_consistent (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) (before : State count) (result : Value × State count)
    (prior : Consistent joint before)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count) work).run before)) :
    Consistent joint result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (Consistent joint)
    (fun query current valid next reached => query_consistent joint count query current next valid reached)
    work before prior result supported

/-- The actual ordinary report experiment uses precisely the native transcript snapshot, including failed signing-publication paths. -/
theorem run_snapshot (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) (result : Value × State count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count work)) :
    result.2.1.snapshot = RegistrationNativeIdentityHistoryReport.snapshot joint count result.2.2.source.2 := by
  have consistent := program_consistent joint count work (initial count) result (initial_consistent joint count) supported
  exact consistent.1.1.trans (RegistrationNativeIdentityReportSnapshot.reporting_snapshot joint result.2.2 consistent.2)

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.query_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.query_consistent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.initial_consistent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.initial_consistent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.program_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.program_consistent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.run_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor.run_snapshot
