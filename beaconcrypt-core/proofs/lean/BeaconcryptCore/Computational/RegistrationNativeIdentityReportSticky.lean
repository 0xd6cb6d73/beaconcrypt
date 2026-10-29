-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor

/-! A native pre-accept origin report remains recognized through every later ordinary joint-service interaction and candidate report. Freshness is tested at the report; subsequent signing, key creation or compromise cannot erase its sticky event. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportSticky
open RegistrationNativeIdentityReportMonitor (State)
open PqxdhJointPhase1Reports (ProtocolSpec)
variable {Value : Type}

theorem query_sticky (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : ProtocolSpec.Domain)
    (before : State count) (result : ProtocolSpec.Range query × State count)
    (compatible : PqxdhJointPhase1Reports.Compatible before.1 before.2) (occurred : before.1.occurred = true)
    (supported : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count query).run before)) :
    PqxdhJointPhase1Reports.Compatible result.2.1 result.2.2 ∧ result.2.1.occurred = true := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, reached, returned⟩ := OracleComp.mem_support_map_peel _ _ supported
  cases returned
  have matched := PqxdhJointPhase1Reports.wrapper_source_preserves joint count query before.1 before.2 compatible inner reached
  have earlier : before.2.occurred = true := compatible.2.symm.trans occurred
  have retained := OracleComp.simulateQ_run_preserves_inv_of_query
    (PqxdhDynamicIdentityReports.reportingImpl joint count) (fun current => current.occurred = true)
    (PqxdhDynamicIdentityReports.reportingImpl_occurred joint count)
    ((PqxdhJointPhase1Reports.wrapper joint count query).run before.1) before.2 earlier inner reached
  exact ⟨matched, matched.2.trans retained⟩

/-- Arbitrary complete later work retains the report-time native origin event without a report-position factor. -/
theorem program_sticky (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) (before : State count) (result : Value × State count)
    (compatible : PqxdhJointPhase1Reports.Compatible before.1 before.2) (occurred : before.1.occurred = true)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count) work).run before)) :
    result.2.1.occurred = true := by
  have preserved := OracleComp.simulateQ_run_preserves_inv_of_query _
    (fun current : State count => PqxdhJointPhase1Reports.Compatible current.1 current.2 ∧ current.1.occurred = true)
    (fun query current prior next reached => query_sticky joint count query current next prior.1 prior.2 reached)
    work before ⟨compatible, occurred⟩ result supported
  exact preserved.2

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportSticky

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSticky.query_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSticky.query_sticky
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSticky.program_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSticky.program_sticky
