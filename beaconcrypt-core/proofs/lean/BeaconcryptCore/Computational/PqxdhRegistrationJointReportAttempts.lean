-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts

/-! Every original-candidate verification attempt has an explicit cap through both actual source and ordinary-identity compilers. Local public reporting is separate from cryptographic oracle calls. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts
open PqxdhRegistrationJointReportLift (Spec lift erase extend)
variable {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ} {Result S : Type}

def IsReport : (ι ⊕ PqxdhJointPhase1Reports.CandidateReport) → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred (IsReport (ι := ι)) :=
  fun query => by cases query <;> simp only [IsReport] <;> infer_instance

/-- Forwarding the complete original computation cannot manufacture a candidate-report attempt. Its cryptographic work remains in that original computation. -/
theorem lift_free (program : OracleComp source Result) : (lift program).IsQueryBoundP IsReport 0 := by
  unfold lift
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, isQueryBoundP_query_bind_iff,
        IsReport, not_false_eq_true, true_or, true_and]
      exact ih

/-- An extended stateful compiler forwards exactly one public report or executes the whole original callback without adding reports. -/
theorem extend_step (impl : QueryImpl source (StateT S (OracleComp target)))
    (query : (Spec source).Domain) (state : S) :
    ((extend impl query).run state).IsQueryBoundP IsReport (if IsReport query then 1 else 0) := by
  cases query with
  | inl query =>
      change (lift (impl query state)).IsQueryBoundP IsReport 0
      exact lift_free (impl query state)
  | inr report => simp [extend, StateT.run, IsReport, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- The entire adaptive source compiler preserves the public attempt cap for every possible original or report reply and all retained local state. -/
theorem extend_bound (impl : QueryImpl source (StateT S (OracleComp target)))
    (program : OracleComp (Spec source) Result) (bound : Nat)
    (bounded : program.IsQueryBoundP IsReport bound) (state : S) :
    ((simulateQ (extend impl) program).run state).IsQueryBoundP IsReport bound :=
  bounded.simulateQ_run_StateT_of_step (extend_step impl) state

/-- Each enumerated generated index consumes one counted original-candidate report attempt. -/
theorem batch_bound (indices : List Nat) (candidate : PqxdhEd25519EufCma.Phase1Candidate) :
    (PqxdhRegistrationJointRawReports.batch (source := source) indices candidate).IsQueryBoundP IsReport indices.length := by
  induction indices with
  | nil => simp [PqxdhRegistrationJointRawReports.batch]
  | cons index rest ih =>
      simp [PqxdhRegistrationJointRawReports.batch, isQueryBoundP_query_bind_iff, IsReport, ih]

variable {KemSK Reader Response : Type}

def attemptCost (count : Nat) (kind : PqxdhRegistrationJointRevealCosts.SourceKind) : Nat :=
  if kind = .inl 3 then count else 0

/-- A source acceptance attempt emits at most one full bounded-target batch; every other command emits zero candidate reports. Failure and malformed-input branches stay included. -/
theorem report_bound (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (answer : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query) :
    (PqxdhRegistrationJointRawReports.report (source := source) codec count query answer).IsQueryBoundP IsReport
      (attemptCost count (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query)) := by
  rcases query with (coin | request) | request
  · simp [PqxdhRegistrationJointRawReports.report]
  · cases request <;> try simp [PqxdhRegistrationJointRawReports.report]
    rename_i raw
    cases answer with
    | none => simp
    | some index =>
        dsimp
        split
        · simp
        · simpa only [List.length_range, attemptCost, PqxdhRegistrationJointRevealCosts.sourceKind,
            PqxdhRegistrationSchedule.sourceKind, ite_true] using batch_bound (source := source) (List.range count) _
  · simp [PqxdhRegistrationJointRawReports.report]

/-- The original command query is not a report; only its explicit post-answer batch consumes this allowance. -/
theorem instrument_step (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) :
    (PqxdhRegistrationJointRawReports.instrument codec count query).IsQueryBoundP IsReport
      (attemptCost count (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query)) := by
  simp only [PqxdhRegistrationJointRawReports.instrument, isQueryBoundP_query_bind_iff,
    IsReport, not_false_eq_true, true_or, true_and]
  intro answer
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact report_bound codec count query answer

def accounting (impl : QueryImpl source (OracleComp target)) :
    QueryImpl source (StateT Unit (OracleComp target)) :=
  fun query before => (fun answer => (answer, before)) <$> impl query

/-- Adding an inert accounting coordinate retains the full original stateless program. This helper supplies the existing checked weighted stateful ledger without inventing source work. -/
theorem accounting_state (impl : QueryImpl source (OracleComp target))
    (program : OracleComp source Result) (state : Unit) :
    (simulateQ (accounting impl) program).run state =
      (fun result => (result, state)) <$> simulateQ impl program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (((fun answer => (answer, state)) <$> impl query) >>= fun result =>
        (simulateQ (accounting impl) (next result.1)).run result.2) = _
      simp only [bind_map_left, ih, map_bind]

/-- The complete adaptive command tree emits at most N times the number of raw acceptance attempts, counting every generated-index report separately. -/
theorem instrument_bound (codec : PqxdhServerAuthExperiment.Codec Reader Response) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (simulateQ (PqxdhRegistrationJointRawReports.instrument codec count) program).IsQueryBoundP IsReport
      (count * budget (.inl 3)) := by
  have bounded := FinitePartitionQueryBounds.weighted_bound
    (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK)) (attemptCost count) budget
    (accounting (PqxdhRegistrationJointRawReports.instrument codec count)) IsReport program certified
    (fun query state => by
      simpa only [accounting, StateT.run, isQueryBoundP_map_iff] using instrument_step codec count query) ()
  rw [accounting_state, isQueryBoundP_map_iff] at bounded
  simpa [attemptCost, ite_mul] using bounded

variable {baseSpec : OracleSpec ι} {A : Type}
open PqxdhServerAuthExperiment

/-- Literal initialization creates no candidate report; the same exact N*qAccept cap survives every source command, optional constructor result and complete owner/native continuation. -/
theorem initialized_commands_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhRegistrationJointReportCommands.initialized setup codec checks supplied count program).IsQueryBoundP IsReport
      (count * budget (.inl 3)) := by
  unfold PqxdhRegistrationJointReportCommands.initialized
  rw [← Nat.zero_add (count * budget (.inl 3))]
  apply isQueryBoundP_bind (lift_free _)
  rintro (_ | created) _
  · simp
  · rw [isQueryBoundP_map_iff]
    exact extend_bound _ _ _ (instrument_bound codec count program budget certified) _

/-- The concrete ordinary-joint-game reduction has the same N*qAccept original-candidate verification cap. Both local/private compilers forward each report once and add no hidden acceptance attempt. -/
theorem initialized_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime).IsQueryBoundP
      PqxdhJointPhase1Reports.IsCandidateReport (count * budget (.inl 3)) := by
  have compiled := extend_bound (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit) _ _
    (initialized_commands_bound setup codec checks supplied count program budget certified) (PqxdhLiveKemBirth.empty, runtime)
  have routed := extend_bound (PqxdhRegistrationJointIdentityRouting.route setup.joint) _ _ compiled ⟨[], []⟩
  exact (isQueryBoundP_congr_pred (fun query => by cases query <;> rfl)).mp routed

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.lift_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.lift_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.extend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.extend_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.extend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.extend_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.batch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.batch_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.report_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.report_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.instrument_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.instrument_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.accounting_state' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.accounting_state

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.instrument_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.instrument_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.initialized_commands_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.initialized_commands_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.initialized_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts.initialized_bound
