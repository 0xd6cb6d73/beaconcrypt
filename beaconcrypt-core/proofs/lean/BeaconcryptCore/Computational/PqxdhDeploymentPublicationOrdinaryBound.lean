-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySelection
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient

/-! The original unissued-field branch uses the existing CE-A2 client and its ordinary joint-use weak-EUF reductions. The global bundle audit is erased exactly, with complete private signing history retained. Failed publication is allowed throughout; freshness follows from the compiled program's zero private-read caps. -/

open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhEd25519EufCma
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentProvenance (acceptedCandidates finalTranscript)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The ordinary event needs only the encoded full source result, including its actual signing pool. Owner seeds and the bundle-occurrence audit do not enter the event. -/
def EncodedEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (output : Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK
      (PqxdhDeploymentPublicationSecurityExecution.Result X))) : Prop :=
  ∃ outcome, output = some outcome ∧ ∃ index candidate decoded,
    candidate ∈ acceptedCandidates codec outcome.2.1.1.2.transcript ∧
      ∃ publicKey, PqxdhDynamicIdentityReports.sourceKeys setup.joint outcome.2.2.pool.1.seeds index = some publicKey ∧
        acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded) ∧
        ∃ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
          field.message ∉ PqxdhRegistrationJointSigningTranscript.messagesAt index outcome.2.2.pool.1.transcript

def encoded (setup : Setup baseSpec KemSK)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.Outcome KemSK A X) :=
  outcome.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup ∘
    PqxdhDeploymentPublicationSecurityAudit.erase)

/-- The ordinary event is preserved pointwise by the exact audit-erasure and native-encoding projection. -/
theorem ordinary_encoded (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.Outcome KemSK A X) :
    PqxdhDeploymentPublicationSecuritySelection.OrdinaryEvent setup codec outcome ↔
      EncodedEvent setup codec (encoded setup outcome) := by
  rcases outcome with ⟨_ | ⟨created, result, native, audit⟩, after⟩
  · simp [PqxdhDeploymentPublicationSecuritySelection.OrdinaryEvent, EncodedEvent, encoded]
  · simp [PqxdhDeploymentPublicationSecuritySelection.OrdinaryEvent,
      PqxdhDeploymentPublicationSecuritySelection.AcceptedAt, PqxdhRegistrationJointAttemptOrigin.Unissued,
      EncodedEvent, encoded, PqxdhDeploymentPublicationSecurityAudit.erase,
      PqxdhRegistrationJointInitializedSchedule.encodeOutcome, PqxdhRegistrationJointGeneratedFinish.encodeState]
    constructor
    · rintro ⟨index, candidate, member, ⟨decoded, publicKey, key, accepted⟩, unissued⟩
      exact ⟨index, candidate, member, decoded, publicKey, key, accepted, unissued⟩
    · rintro ⟨index, candidate, member, decoded, publicKey, key, accepted, unissued⟩
      exact ⟨index, candidate, member, ⟨decoded, publicKey, key, accepted⟩, unissued⟩

/-- The real audited execution and the existing original report client have the same encoded complete source outcome. Only the public report monitor and private bundle audit are forgotten. -/
theorem encoded_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A) :
    encoded setup <$> PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode
        adversary runtime =
      (fun reached => (sourceResult reached).1) <$> PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
          (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime) := by
  have audited := congrArg (Functor.map (fun result =>
      result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup)))
    (PqxdhDeploymentPublicationSecurityAudit.source setup codec checks ensureInit none
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  have reported := congrArg (Functor.map Prod.fst)
    (PqxdhRegistrationJointReportSource.initialized_source setup codec checks ensureInit none count
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime)
  simp only [Functor.map_map] at audited reported
  have projection : encoded setup = fun outcome : PqxdhDeploymentPublicationSecurityAudit.Outcome KemSK A X =>
      (outcome.1.map PqxdhDeploymentPublicationSecurityAudit.erase).map
        (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup) := by
    funext outcome
    rw [Option.map_map]
    rfl
  rw [projection]
  exact audited.trans reported.symm

private theorem source_transcript (count : Nat)
    (reached : ReportResult KemSK A (PqxdhDeploymentPublicationSecurityExecution.Result X) count)
    (outcome : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK
      (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (finished : (sourceResult reached).1 = some outcome) :
    finalTranscript reached.1 = outcome.2.1.1.2.transcript := by
  change reached.1.1.1.map (PqxdhRegistrationJointOpenInitialization.attach (sourceResult reached).2.1) =
    some outcome at finished
  obtain ⟨original, found, rfl⟩ := Option.map_eq_some_iff.mp finished
  simp only [finalTranscript, found, Option.map_some, Option.getD_some,
    PqxdhRegistrationJointOpenInitialization.attach]

/-- An ordinary actual source event becomes an original-field failure in the same final report snapshot. The complete failed-writer signing history is used; no publication-success restriction is imposed. -/
theorem report_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (reached : ReportResult KemSK A (PqxdhDeploymentPublicationSecurityExecution.Result X) (budget.create + 1))
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint (budget.create + 1)
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none (budget.create + 1)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime)))
    (ordinary : EncodedEvent setup codec (sourceResult reached).1) :
    ∃ target candidate, candidate ∈ acceptedCandidates codec (finalTranscript reached.1) ∧
      PqxdhJointPhase1Reports.FieldOriginFailure setup.joint ⟨target, candidate⟩ reached.2.1.snapshot := by
  obtain ⟨outcome, finished, index, candidate, decoded, member, publicKey, key, accepted, unissued⟩ := ordinary
  have pool := PqxdhRegistrationJointInitializedReports.outcome_pool reached outcome finished
  rw [pool] at key unissued
  have hasSeed := key
  rw [PqxdhDynamicIdentityReports.sourceKeys, Option.map_eq_some_iff] at hasSeed
  obtain ⟨seed, seedFound, _⟩ := hasSeed
  change (reached.1.2.refs.map (PqxdhRegistrationJointIdentityRouting.resolve reached.2.2.source.2.seeds))[index]? =
    some seed at seedFound
  rw [List.getElem?_map, Option.map_eq_some_iff] at seedFound
  obtain ⟨ref, refFound, _⟩ := seedFound
  obtain ⟨target, rfl⟩ := PqxdhDeploymentPublishedTuple.report_generated setup codec checks ensureInit
    (budget.create + 1) _ runtime reached supported index ref refFound
  have creates := PqxdhRegistrationJointReportCosts.initialized_creates setup codec checks ensureInit none
    (budget.create + 1) (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime
    (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
  have targetBound := PqxdhDeploymentPublishedTuple.generated_lt setup codec checks ensureInit (budget.create + 1) _
    runtime (creates.mono (by simp [PqxdhDeploymentCompileCaps.transported]; omega)) reached supported index target refFound
  obtain ⟨original, actual, same⟩ := PqxdhRegistrationJointInitializedReports.source_witness setup codec checks ensureInit
    none (budget.create + 1) _ runtime reached supported
  have quiet := PqxdhDeploymentQuiet.quiet_initialized setup codec checks ensureInit none
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
    (PqxdhDeploymentCompileSecrecy.compile_full_unread setup codec route bounds mode adversary 0 (by decide))
    (PqxdhDeploymentCompileSecrecy.compile_full_unread setup codec route bounds mode adversary 1 (by decide))
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) PqxdhDeploymentQuiet.quiet_empty
    original actual
  have finalPool : original.2 = (sourceResult reached).2 := congrArg Prod.snd same
  rw [finalPool] at quiet
  refine ⟨target, candidate, ?_, ?_⟩
  · rw [source_transcript (budget.create + 1) reached outcome finished]
    exact member
  · exact PqxdhRegistrationJointInitializedReports.field_origin setup codec checks ensureInit none (budget.create + 1)
      _ runtime reached supported index ⟨target, targetBound⟩ refFound publicKey candidate decoded key accepted
      (PqxdhDeploymentQuiet.unrevealed_of_quiet _ quiet index) unissued

/-- Exact ordinary-event probability transfer from the actual global audit to the original CE-A2 report run. No codec correctness law is needed to erase this analysis audit. -/
theorem ordinary_report_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A) :
    Pr{let outcome ← PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode
        adversary runtime}[PqxdhDeploymentPublicationSecuritySelection.OrdinaryEvent setup codec outcome] =
      Pr{let reached ← PqxdhJointPhase1Reports.run setup.joint count
            (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
              (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime)}[
        EncodedEvent setup codec (sourceResult reached).1] := by
  calc
    _ = Pr{let outcome ← PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds
            mode adversary runtime}[EncodedEvent setup codec (encoded setup outcome)] :=
      prEvent_congr _ _ _ (ordinary_encoded setup codec)
    _ = _ := by
      rw [← prEvent_map, encoded_actual setup codec checks route ensureInit bounds mode adversary count runtime,
        prEvent_map]

/-- The actual ordinary branch is bounded by the existing CE-A2 family's ordinary joint-use weak-EUF advantages, with coefficient one. Failed Fresh publication calls are unrestricted, and the old reductions and all their resource bills are reused unchanged. -/
theorem ordinary_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    Pr{let outcome ← PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode
        adversary runtime}[PqxdhDeploymentPublicationSecuritySelection.OrdinaryEvent setup codec outcome] ≤
      ∑ target : Fin (budget.create + 1), advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target) := by
  classical
  rw [ordinary_report_probability setup codec checks route ensureInit bounds mode adversary (budget.create + 1) runtime]
  have transfer := PqxdhDeploymentProvenance.client_transfer setup codec checks route ensureInit bounds mode adversary
    (budget.create + 1) runtime (fun reached => EncodedEvent setup codec (sourceResult reached).1)
    (fun reached supported ordinary after afterMember => by
      obtain ⟨target, candidate, member, failure⟩ := report_failure setup codec checks route ensureInit bounds mode
        adversary budget respects runtime reached supported ordinary
      exact PqxdhDeploymentPublishedTuple.announceAll_detects setup.joint (budget.create + 1) target _ candidate member
        reached.2 failure after afterMember)
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map, ← prEvent_eq_evalDist_singleton _ true, prEvent_map]
    at transfer
  simp only [decide_eq_true_eq] at transfer
  refine transfer.trans ?_
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint budget.create _ fallback ordinaryFallback
    ((PqxdhDeploymentProvenance.client_creates setup codec checks route ensureInit bounds mode adversary budget respects
      (budget.create + 1) runtime).mono (by omega))

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.ordinary_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.ordinary_encoded

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.encoded_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.encoded_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.report_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.report_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.ordinary_report_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.ordinary_report_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.ordinary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationOrdinaryBound.ordinary_bound
