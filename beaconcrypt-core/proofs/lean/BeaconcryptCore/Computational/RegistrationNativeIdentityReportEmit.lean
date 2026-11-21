-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor

/-! Native pre-accept reporting forwards every generated public-key alias. Each report keeps the same source snapshot and sets the ordinary sticky origin event exactly when that unchanged candidate is recognized. The result follows from the actual report interpreter, including all subsequent reports in the alias list. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit
open PqxdhJointPhase1Reports (ProtocolSpec CandidateReport)
open RegistrationNativeIdentityReportMonitor (State)
variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}

theorem report_fields (joint : PqxdhJointIdentity.Primitives) (count : Nat) (report : CandidateReport)
    (before : State count) (result : Unit × State count)
    (supported : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count (.inr report)).run before)) :
    result.2.1.snapshot = before.1.snapshot ∧
      result.2.1.occurred = (before.1.occurred || PqxdhJointPhase1Reports.candidateAccepted joint report before.1.snapshot) := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, reached, returned⟩ := OracleComp.mem_support_map_peel _ _ supported
  cases returned
  cases translated : PqxdhJointPhase1Reports.translateReport joint report before.1.snapshot with
  | none =>
      simp only [PqxdhJointPhase1Reports.wrapper, StateT.run, translated, simulateQ_pure] at reached
      subst inner
      exact ⟨rfl, rfl⟩
  | some forgery =>
      simp only [PqxdhJointPhase1Reports.wrapper, StateT.run, translated, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure] at reached
      subst inner
      exact ⟨rfl, rfl⟩

/-- Reporting aliases changes no public source snapshot and cannot erase an earlier recognized origin event. -/
theorem emit_fields (joint : PqxdhJointIdentity.Primitives) (count : Nat) (reports : List CandidateReport)
    (before : State count) (result : Unit × State count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      (RegistrationNativeIdentityMain.emit reports)).run before)) :
    result.2.1.snapshot = before.1.snapshot ∧
      (before.1.occurred = true → result.2.1.occurred = true) := by
  induction reports generalizing before with
  | nil =>
      simp only [RegistrationNativeIdentityMain.emit, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, id⟩
  | cons report rest ih =>
      simp only [RegistrationNativeIdentityMain.emit, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have first := report_fields joint count report before middle reached
      have later := ih middle.2 continued
      refine ⟨later.1.trans first.1, fun occurred => later.2 ?_⟩
      rw [first.2, occurred]
      rfl

/-- One recognized candidate anywhere in the actual alias report list sets the same ordinary origin event without choosing an alias position. -/
theorem emit_detects (joint : PqxdhJointIdentity.Primitives) (count : Nat) (reports : List CandidateReport)
    (report : CandidateReport) (member : report ∈ reports) (before : State count) (result : Unit × State count)
    (recognized : PqxdhJointPhase1Reports.candidateAccepted joint report before.1.snapshot = true)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      (RegistrationNativeIdentityMain.emit reports)).run before)) : result.2.1.occurred = true := by
  induction reports generalizing before with
  | nil => cases member
  | cons first rest ih =>
      simp only [RegistrationNativeIdentityMain.emit, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have fields := report_fields joint count first before middle reached
      rcases List.mem_cons.mp member with same | later
      · subst report
        apply (emit_fields joint count rest middle.2 result continued).2
        rw [fields.2, recognized]
        exact Bool.or_true _
      · apply ih later middle.2 _ continued
        rw [fields.1]
        exact recognized

/-- The actual native pre-accept operation records any recognized generated-key alias before SDK authentication continues. -/
theorem report_detects (joint : PqxdhJointIdentity.Primitives) (count : Nat) (packet : beaconcrypt_core.registration.InitPacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source) (monitor : State count)
    (result : (Unit × RegistrationNativeIdentityMain.State n KemSK source) × State count)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ before.beacons)
    (matched : PqxdhEd25519EufCma.encodedIdentity owner.identity.publicIdentity.ed25519 =
      PqxdhRefinement.absBytes packet.identity_key)
    (recognized : PqxdhJointPhase1Reports.candidateAccepted joint ⟨owner.identity.handle, RegistrationRootInput.candidate packet⟩ monitor.1.snapshot = true)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      ((RegistrationNativeIdentityMain.report packet).run before)).run monitor)) : result.2.1.occurred = true := by
  simp only [RegistrationNativeIdentityMain.report, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  exact emit_detects joint count (RegistrationNativeIdentityMain.reports packet before.beacons)
    ⟨owner.identity.handle, RegistrationRootInput.candidate packet⟩
    (RegistrationNativeIdentityHistoryReport.reports_owner packet before.beacons owner member matched)
    monitor inner recognized reached

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.report_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.report_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.emit_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.emit_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.emit_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.emit_detects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.report_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit.report_detects
