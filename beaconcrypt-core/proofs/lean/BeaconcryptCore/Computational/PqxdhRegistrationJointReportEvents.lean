-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication

/-! The original public batch detects every eligible generated-index field-origin event and preserves the report-time signing/reveal snapshot. Subsequent source compromise is handled by the existing first-fresh-report endpoint. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents
open PqxdhJointIdentity PqxdhJointPhase1Reports PqxdhDynamicIdentityReports

/-- An original candidate report cannot change any public creation/signing/reveal history used to decide the next report. All actual private requests remain outside this reporting step. -/
theorem report_snapshot (joint : Primitives) (count : Nat) (report : CandidateReport)
    (state : Monitor count) (result : Unit × Monitor count)
    (supported : result ∈ support ((wrapper joint count (.inr report)).run state)) :
    result.2.snapshot = state.snapshot := by
  cases translated : translateReport joint report state.snapshot with
  | none =>
      simp only [wrapper, StateT.run, translated, mem_support_pure_iff] at supported
      subst result
      rfl
  | some forgery =>
      simp only [wrapper, StateT.run, translated, mem_support_bind_iff] at supported
      obtain ⟨answer, _, supported⟩ := supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl

/-- A whole explicit target batch retains the same report-time history and recognizes the disjunction of all original-candidate events, without a guessed field or report position. -/
theorem batch_events (joint : Primitives) (count : Nat) (indices : List Nat)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (state : Monitor count) (result : Unit × Monitor count)
    (supported : result ∈ support ((simulateQ (wrapper joint count)
      (PqxdhRegistrationJointRawReports.batch indices candidate)).run state)) :
    result.2.snapshot = state.snapshot ∧
      result.2.occurred = (state.occurred || indices.any (fun index => candidateAccepted joint ⟨index, candidate⟩ state.snapshot)) := by
  induction indices generalizing state result with
  | nil =>
      simp only [PqxdhRegistrationJointRawReports.batch, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, by simp⟩
  | cons index rest ih =>
      simp only [PqxdhRegistrationJointRawReports.batch, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      obtain ⟨reply, step, tail⟩ := (mem_support_bind_iff _ _ _).mp supported
      have snapshot := report_snapshot joint count ⟨index, candidate⟩ state reply step
      have occurrence := (wrapper_observation joint count (.inr ⟨index, candidate⟩) state reply step).2.2
      have remaining := ih reply.2 result tail
      refine ⟨remaining.1.trans snapshot, ?_⟩
      rw [remaining.2, snapshot, occurrence]
      simp only [List.any_cons, Bool.or_assoc]

/-- Every fresh accepted unissued field under any generated target is detected by the same original-candidate batch. There is no honest-target premise and no additional probability selection. -/
theorem batch_detects (joint : Primitives) (count target : Nat)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (state : Monitor count) (result : Unit × Monitor count)
    (failure : FieldOriginFailure joint ⟨target, candidate⟩ state.snapshot)
    (supported : result ∈ support ((simulateQ (wrapper joint count)
      (PqxdhRegistrationJointRawReports.batch (List.range count) candidate)).run state)) :
    result.2.occurred = true := by
  rw [(batch_events joint count (List.range count) candidate state result supported).2, Bool.or_eq_true]
  exact Or.inr (List.any_eq_true.mpr ⟨target, List.mem_range.mpr failure.1,
    (candidateAccepted_iff joint ⟨target, candidate⟩ state.snapshot).mpr failure⟩)

/-- The exact public reporting code after a successful raw source reply detects its unchanged eligible candidate. Malformed inputs cannot satisfy the exact source-getter equation. -/
theorem raw_detects {KemSK Reader Response : Type} (joint : Primitives) (count target : Nat)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (raw : Pqxdh.Bytes) (session : Nat)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (state : Monitor count) (result : Unit × Monitor count)
    (original : PqxdhRegistrationJointRawSignatures.candidate codec raw = some candidate)
    (failure : FieldOriginFailure joint ⟨target, candidate⟩ state.snapshot)
    (supported : result ∈ support ((simulateQ (wrapper joint count)
      (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count (.inl (.inr (.accept raw))) (some session))).run state)) :
    result.2.occurred = true := by
  simp only [PqxdhRegistrationJointRawReports.report, original] at supported
  exact batch_detects joint count target candidate state result failure supported

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.report_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.report_snapshot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.batch_events' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.batch_events

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.batch_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.batch_detects

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.raw_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents.raw_detects
