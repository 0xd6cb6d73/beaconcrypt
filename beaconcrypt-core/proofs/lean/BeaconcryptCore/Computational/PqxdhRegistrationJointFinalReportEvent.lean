-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate

/-! Probability transport from a chosen final original candidate to the ordinary public field-report event. No field or report-position selection is sampled. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointFinalReportEvent
open PqxdhJointIdentity PqxdhJointPhase1Reports PqxdhDynamicIdentityReports
open PqxdhRegistrationJointFinalCandidate

/-- A failure in the actual pre-report snapshot is detected with probability one by the finite terminal batch. -/
theorem announce_hits (joint : Primitives) (count target : Nat)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (state : Monitor count × ReportingState count)
    (failure : FieldOriginFailure joint ⟨target, candidate⟩ state.1.snapshot) :
    𝒟[(fun result => result.2.1.occurred) <$>
      (simulateQ (sourceImpl joint count) (announce count (some candidate))).run state] {true} = 1 := by
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  apply OracleComp.prEvent_eq_one_of_forall_mem_support
  intro result supported
  apply PqxdhRegistrationJointTerminalReports.source_detects joint count target candidate state result supported
  rw [(PqxdhRegistrationJointTerminalReports.source_batch joint count (List.range count) candidate state result supported).1]
  exact failure

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}
open PqxdhServerAuthExperiment
open PqxdhRegistrationJointInitializedReports (ReportResult)

/-- Eligibility is checked at the actual stopping snapshot; the raw candidate is the adversary's returned public input. -/
def Failure (joint : Primitives) (codec : Codec Reader Response) {count : Nat}
    (result : ReportResult KemSK A Choice count) : Prop :=
  ∃ target candidate, selected codec result.1 = some candidate ∧
    FieldOriginFailure joint ⟨target, candidate⟩ result.2.1.snapshot

/-- Appending the public terminal batch bounds the chosen final source report event with coefficient one. -/
theorem transport (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A) :
    letI := Classical.propDecidable
    𝒟[(fun result => decide (Failure setup.joint codec result)) <$>
      run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime)] {true} ≤
    𝒟[(fun result => result.2.1.occurred) <$>
      run setup.joint count (client setup codec checks ensureInit supplied count program runtime)] {true} := by
  classical
  have bounded := prEvent_bind_mono_of_forall_le_of_support
    (run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime))
    (fun before => (pure (decide (Failure setup.joint codec before)) : ProbComp Bool))
    (fun before => (fun after => after.2.1.occurred) <$>
      (simulateQ (sourceImpl setup.joint count) (announce count (selected codec before.1))).run before.2)
    (fun value : Bool => value = true) (fun value : Bool => value = true) (fun before _ => ?_)
  · rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton] at bounded
    simpa only [client, PqxdhJointPhase1Reports.run, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      simulateQ_map, StateT.run_map, Functor.map_map,
      map_bind, map_pure, bind_assoc, pure_bind, bind_pure_comp] using bounded
  · by_cases failed : Failure setup.joint codec before
    · simp only [prEvent_pure, decide_eq_true_eq, failed, ite_true]
      obtain ⟨target, candidate, chosen, failure⟩ := failed
      rw [chosen]
      have detected := announce_hits setup.joint count target candidate before.2 failure
      rw [← prEvent_eq_evalDist_singleton _ true] at detected
      exact detected.ge
    · simp only [prEvent_pure, decide_eq_true_eq, failed, ite_false, zero_le]

end BeaconcryptCore.Computational.PqxdhRegistrationJointFinalReportEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalReportEvent.announce_hits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalReportEvent.announce_hits

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalReportEvent.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalReportEvent.transport
