-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointTerminalReports

/-! A chosen original candidate at the stopping point of the actual adaptive source scheduler. The reduction reads only the adversary's returned raw bytes, and appends one explicitly counted public target batch. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate
open PqxdhJointPhase1Reports PqxdhRegistrationJointRawReports
open PqxdhRegistrationJointReportLift (erase)
open PqxdhServerAuthExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}

abbrev Choice := Nat × Pqxdh.Bytes
abbrev Output (KemSK A : Type) :=
  (Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK Choice) ×
    PqxdhRegistrationJointIdentityCompiler.Local KemSK A) × PqxdhRegistrationJointIdentityRouting.Registry

/-- Read the literal chosen network candidate from the original adversary's result. Local private state never participates in this projection. -/
def selected (codec : Codec Reader Response) (output : Output KemSK A) :
    Option PqxdhEd25519EufCma.Phase1Candidate :=
  output.1.1.bind fun result => PqxdhRegistrationJointRawSignatures.candidate codec result.2.1.2

/-- Constructor or parser failure emits no candidate; all other original candidates receive one complete generated-index batch. -/
def announce (count : Nat) (candidate : Option PqxdhEd25519EufCma.Phase1Candidate) : OracleComp ProtocolSpec Unit :=
  match candidate with
  | none => pure ()
  | some candidate => batch (List.range count) candidate

/-- The native adaptive scheduler runs first, unchanged. The final public batch consumes only its returned raw candidate and preserves its entire result. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A) :
    OracleComp ProtocolSpec (Output KemSK A) := do
  let result ← PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime
  announce count (selected codec result)
  pure result

/-- The final extra reports erase without changing any original request or result. -/
theorem announce_erase (count : Nat) (candidate : Option PqxdhEd25519EufCma.Phase1Candidate) :
    simulateQ erase (announce count candidate) = pure () := by
  cases candidate with
  | none => rfl
  | some candidate => exact batch_erase (List.range count) candidate

/-- Removing only the report instrumentation restores the literal complete initialized source client. -/
theorem client_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A) :
    simulateQ erase (client setup codec checks ensureInit supplied count program runtime) =
      PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit supplied program runtime := by
  simp only [client, simulateQ_bind, announce_erase, simulateQ_pure, pure_bind, bind_pure,
    PqxdhRegistrationJointReportCompiler.initialized_erase]

set_option backward.isDefEq.respectTransparency false in
/-- The final-report experiment projects to the same complete native initialized execution, retaining private pools, owners, local state, runtime and the original chosen bytes. -/
theorem source_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A) :
    PqxdhRegistrationJointInitializedReports.sourceResult <$>
      run setup.joint count (client setup codec checks ensureInit supplied count program runtime) =
      (fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) := by
  change (fun result => PqxdhRegistrationJointIdentityCompiler.initializedResult (result.1, result.2.2.source.2)) <$>
    run setup.joint count (client setup codec checks ensureInit supplied count program runtime) = _
  have projected := PqxdhRegistrationJointReportSource.program_projection setup.joint count
    (client setup codec checks ensureInit supplied count program runtime)
    (initialMonitor count, ⟨PqxdhDynamicIdentityReports.initialSource count,
      PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩)
  have complete := congrArg (fun work => PqxdhRegistrationJointIdentityCompiler.initializedResult <$> work) projected
  rw [client_erase] at complete
  simpa only [run, Functor.map_map, PqxdhRegistrationJointInitializedReports.sourceResult] using complete.trans
    (PqxdhRegistrationJointIdentityCompiler.initialized_source setup codec checks ensureInit supplied program runtime)

/-- Every original private or uniform class keeps its exact all-reply cap; the public terminal batch has the fixed Unit response. -/
theorem client_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (predicate : PqxdhDynamicIdentityPool.DynamicSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (bounded : (PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit supplied program runtime).IsQueryBoundP predicate bound) :
    (client setup codec checks ensureInit supplied count program runtime).IsQueryBoundP (SourceClass predicate) bound := by
  have erased : (simulateQ erase (client setup codec checks ensureInit supplied count program runtime)).IsQueryBoundP predicate bound := by
    rw [client_erase]
    exact bounded
  have lifted := (PqxdhRegistrationJointReportCosts.erase_bound predicate _ bound).mp erased
  exact (isQueryBoundP_congr_pred (fun query => by cases query <;> rfl)).mp lifted

/-- The additional stopping-point batch makes at most N public report attempts, including parser failure. -/
theorem announce_bound (count : Nat) (candidate : Option PqxdhEd25519EufCma.Phase1Candidate) :
    (announce count candidate).IsQueryBoundP IsCandidateReport count := by
  cases candidate with
  | none => simp [announce]
  | some candidate =>
      have bounded := PqxdhRegistrationJointReportAttempts.batch_bound
        (source := PqxdhDynamicIdentityPool.DynamicSpec) (List.range count) candidate
      rw [List.length_range] at bounded
      exact (isQueryBoundP_congr_pred (fun query => by cases query <;> rfl)).mp bounded

/-- Source acceptances and the chosen stopping candidate are all charged: at most N*(qAccept+1) public reports. -/
theorem reports_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (client setup codec checks ensureInit supplied count program runtime).IsQueryBoundP IsCandidateReport
      (count * (budget (.inl 3) + 1)) := by
  have first := PqxdhRegistrationJointReportAttempts.initialized_bound setup codec checks ensureInit supplied count program runtime budget certified
  have bounded := isQueryBoundP_bind first (fun result _ =>
    (isQueryBoundP_map_iff _ (fun _ : Unit => result) _).mpr (announce_bound count (selected codec result)))
  simpa only [client, bind_pure_comp, Nat.mul_add, Nat.mul_one] using bounded

/-- Every already-derived ordinary source-class cap survives the terminal batch exactly. -/
theorem reported_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (predicate : PqxdhDynamicIdentityPool.DynamicSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (bounded : (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime).IsQueryBoundP
      (SourceClass predicate) bound) :
    (client setup codec checks ensureInit supplied count program runtime).IsQueryBoundP (SourceClass predicate) bound := by
  have lifted : (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime).IsQueryBoundP
      (PqxdhRegistrationJointReportCosts.original predicate) bound :=
    (isQueryBoundP_congr_pred (fun query => by cases query <;> rfl)).mp bounded
  have erased := (PqxdhRegistrationJointReportCosts.erase_bound predicate _ bound).mpr lifted
  rw [PqxdhRegistrationJointReportCompiler.initialized_erase] at erased
  exact client_bound setup codec checks ensureInit supplied count program runtime predicate bound erased

end BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.announce_erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.announce_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.client_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.source_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.source_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.client_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.announce_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.announce_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.reports_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.reports_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.reported_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinalCandidate.reported_bound
