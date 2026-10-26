-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule
import BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript

/-! The ordinary report-time public snapshot uses the actual successful signing log. Combining that fact with the derived source-index routing invariant connects real source signing history to the existing public field-origin detector. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhDynamicIdentityReports
open PqxdhRegistrationJointRoutedHistory (messagesAt)

/-- The public endpoint snapshot is the literal source key map and history, whose signing projection is the actual chronological transcript. -/
def Aligned (joint : Primitives) {count : Nat} (state : ReportingState count) : Prop :=
  state.publicSnapshot = sourceSnapshot joint state.source ∧
    ∀ target : Fin count, signedMessages (state.source.1.histories target) =
      messagesAt target.val state.source.2.transcript

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary source service or public report preserves the same keys, signing history and reveal state in the endpoint snapshot. -/
theorem reporting_query (joint : Primitives) (count : Nat) (request : ReportingSpec.Domain)
    (state : ReportingState count) (aligned : Aligned joint state)
    (result : ReportingSpec.Range request × ReportingState count)
    (supported : result ∈ support ((reportingImpl joint count request).run state)) :
    Aligned joint result.2 := by
  cases request with
  | inr report =>
      obtain rfl := eq_of_mem_support_pure supported
      exact aligned
  | inl request =>
      simp only [reportingImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, actual, returned⟩ := supported
      obtain rfl := eq_of_mem_support_pure returned
      refine ⟨?_, ?_⟩
      · exact (congrArg (observe request answer.1) aligned.1).trans
          (source_snapshot_step joint count request state.source answer actual).symm
      · exact fun target => PqxdhRegistrationJointSigningTranscript.source_step joint target request
          state.source answer (aligned.2 target) actual

/-- Report instrumentation leaves the actual ordinary source invariant intact through the entire linked callback. -/
theorem source_query (joint : Primitives) (count : Nat)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain)
    (state : PqxdhJointPhase1Reports.Monitor count × ReportingState count)
    (aligned : Aligned joint state.2)
    (result : PqxdhJointPhase1Reports.ProtocolSpec.Range request ×
      (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count request).run state)) :
    Aligned joint result.2.2 := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, actual, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact OracleComp.simulateQ_run_preservesInv (reportingImpl joint count) (Aligned joint)
    (fun request state before result member => reporting_query joint count request state before result member)
    _ state.2 aligned inner actual

/-- Every actual report-game prefix uses the generated public keys and complete successful signing history from that very execution. Later source compromise remains available and does not rewrite earlier report snapshots. -/
theorem snapshot {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp PqxdhJointPhase1Reports.ProtocolSpec Result)
    (result : Result × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count work)) :
    result.2.1.snapshot = sourceSnapshot joint result.2.2.source ∧
      ∀ target : Fin count, signedMessages (result.2.1.snapshot.history.histories target) =
        messagesAt target.val result.2.2.source.2.transcript := by
  have aligned := OracleComp.simulateQ_run_preservesInv (PqxdhJointPhase1Reports.sourceImpl joint count)
    (fun state => Aligned joint state.2)
    (fun request state before result member => source_query joint count request state before result member)
    work (PqxdhJointPhase1Reports.initialMonitor count, ⟨initialSource count, initialSnapshot count, false, []⟩)
    ⟨rfl, fun _ => rfl⟩ result supported
  have same := (PqxdhJointPhase1Reports.run_compatible joint count work result supported).1.trans aligned.1
  exact ⟨same, fun target => by rw [same]; exact aligned.2 target⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory.reporting_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory.reporting_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory.source_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory.snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory.snapshot
