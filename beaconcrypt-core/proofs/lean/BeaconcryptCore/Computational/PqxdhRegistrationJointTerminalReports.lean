-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports

/-! Exact terminal public batches through the real stateful source compilers. These equations retain every compiler state coordinate and the complete ordinary report interpreter. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports
open PqxdhRegistrationJointReportLift (Spec extend)
open PqxdhRegistrationJointRawReports (batch)
open PqxdhJointPhase1Reports
variable {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ} {S : Type}

/-- Original reports pass through a stateful compiler without reading or changing its state. -/
theorem extend_batch (impl : QueryImpl source (StateT S (OracleComp target)))
    (indices : List Nat) (candidate : PqxdhEd25519EufCma.Phase1Candidate) (state : S) :
    (simulateQ (extend impl) (batch indices candidate)).run state =
      (fun _ => ((), state)) <$> (batch indices candidate : OracleComp (Spec target) Unit) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [batch, simulateQ_bind, StateT.run_bind]
      simp only [StateT.run] at ih
      simp only [simulateQ_spec_query, extend, StateT.run, bind_map_left, ih, batch, map_bind]
      rfl

/-- Interpreting the ordinary private challenger preserves the batch's exact public snapshot and sticky report event. -/
theorem source_batch (joint : PqxdhJointIdentity.Primitives) (count : Nat) (indices : List Nat)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (state : Monitor count × PqxdhDynamicIdentityReports.ReportingState count)
    (result : Unit × (Monitor count × PqxdhDynamicIdentityReports.ReportingState count))
    (supported : result ∈ support ((simulateQ (sourceImpl joint count) (batch indices candidate)).run state)) :
    result.2.1.snapshot = state.1.snapshot ∧
      result.2.1.occurred = (state.1.occurred || indices.any (fun index => candidateAccepted joint ⟨index, candidate⟩ state.1.snapshot)) := by
  rw [sourceImpl, QueryImpl.Stateful.simulateQ_link_run] at supported
  obtain ⟨inner, actual, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  have reachable : inner.1 ∈ support ((simulateQ (wrapper joint count) (batch indices candidate)).run state.1) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhDynamicIdentityReports.reportingImpl joint count) _ state.2
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, actual, rfl⟩
  exact PqxdhRegistrationJointReportEvents.batch_events joint count indices candidate state.1 inner.1 reachable

/-- The complete local KEM/runtime and generated/imported routing states pass unchanged through the terminal public batch. -/
theorem compiler_batch {j : Type} {baseSpec : OracleSpec j} {KemSK A : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (indices : List Nat) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (localState : PqxdhRegistrationJointIdentityCompiler.Local KemSK A)
    (registry : PqxdhRegistrationJointIdentityRouting.Registry) :
    PqxdhRegistrationJointReportCompiler.reduction setup ensureInit (batch indices candidate) localState registry =
      (fun _ => (((), localState), registry)) <$> (batch indices candidate : OracleComp ProtocolSpec Unit) := by
  simp only [PqxdhRegistrationJointReportCompiler.reduction, extend_batch, simulateQ_map,
    StateT.run_map, Functor.map_map]

/-- Every original-field failure at the final batch snapshot is detected at that same snapshot, with no field or report-position choice. -/
theorem source_detects (joint : PqxdhJointIdentity.Primitives) (count target : Nat)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (state : Monitor count × PqxdhDynamicIdentityReports.ReportingState count)
    (result : Unit × (Monitor count × PqxdhDynamicIdentityReports.ReportingState count))
    (supported : result ∈ support ((simulateQ (sourceImpl joint count) (batch (List.range count) candidate)).run state))
    (failure : FieldOriginFailure joint ⟨target, candidate⟩ result.2.1.snapshot) :
    result.2.1.occurred = true := by
  obtain ⟨snapshot, occurred⟩ := source_batch joint count (List.range count) candidate state result supported
  rw [snapshot] at failure
  rw [occurred, Bool.or_eq_true]
  exact Or.inr (List.any_eq_true.mpr ⟨target, List.mem_range.mpr failure.1,
    (candidateAccepted_iff joint ⟨target, candidate⟩ state.1.snapshot).mpr failure⟩)

/-- Compiling a source prefix and its literal continuation preserves all local and routing state at the cut. -/
theorem compiler_bind {j : Type} {baseSpec : OracleSpec j} {KemSK A X Y : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) X)
    (next : X → OracleComp (Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) Y)
    (localState : PqxdhRegistrationJointIdentityCompiler.Local KemSK A)
    (registry : PqxdhRegistrationJointIdentityRouting.Registry) :
    PqxdhRegistrationJointReportCompiler.reduction setup ensureInit (program >>= next) localState registry =
      (PqxdhRegistrationJointReportCompiler.reduction setup ensureInit program localState registry >>= fun result =>
        PqxdhRegistrationJointReportCompiler.reduction setup ensureInit (next result.1.1) result.1.2 result.2) := by
  simp only [PqxdhRegistrationJointReportCompiler.reduction, simulateQ_bind, StateT.run_bind]

end BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.extend_batch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.extend_batch

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.source_batch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.source_batch

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.compiler_batch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.compiler_batch

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.source_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.source_detects

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.compiler_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports.compiler_bind
