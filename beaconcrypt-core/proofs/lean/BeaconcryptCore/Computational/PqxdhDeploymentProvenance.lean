-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection
import BeaconcryptCore.Computational.PqxdhDeploymentReplay
import BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps

/-! Phase 1 provenance in the common deployment experiment (CE-7, CE-A2, signing-history form). The probability space is the report-instrumented initialized execution of the compiled program of a deployment adversary, with a generated Server seed: `report_game` shows that, projected to the constructed Server's public data, the adversary's output and the whole ledger, it is exactly the deployment experiment in either mode, so the report instrumentation, the private identity and KEM pools and their signing log are analysis state only. Every successful accept is reported at the moment it returns, at every generated identity position. The A2 client (`client`) runs this execution and then one terminal public batch for the raw candidate of every successful accept of the final transcript; the terminal batches serve the published-tuple corollaries and add no identity request (`announceAll_bound`, `client_creates`). `a2_bound` is CE-A2 over all accepts: the probability that the run passes through a successful raw accept whose verified identity key is a generated Beacon owner's, unrevealed at that accept, and whose verified key tuple is not among that owner's chronological signing attempts before the accept, is at most the sum over the `qCreate + 1` generated identity positions of the ordinary joint-use weak-EUF advantages of the A2 client's reductions, with coefficient one; there is no accept-position, owner, field or report-position factor and no collision term. The event is `PqxdhDeploymentAcceptDetection.NativeForgery` of the compiled program; the bound goes through `forgery_detected`, the sticky report flag (`client_transfer`) and `fieldOrigin_advantage_le_sum`. The premises are the attached-signature format rule `shortRejects` with `setup.wiring` and the adversary's budget, which bounds identity creation by `qCreate` plus the generated Server seed. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentProvenance
open PqxdhJointIdentity PqxdhDynamicIdentityReports PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhJointPhase1Reports (ProtocolSpec SourceClass Monitor sourceImpl)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
open PqxdhDeploymentInterface (Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhDeploymentAcceptDetection (NativeForgery)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The raw candidates of the successful accepts of a transcript, oldest first, read from their raw bytes by the codec reader. -/
def acceptedCandidates (codec : Codec Reader Response) (transcript : List Entry) : List Phase1Candidate :=
  transcript.filterMap fun entry => match entry with
    | ⟨.inl (.inr (.accept raw)), some _⟩ => PqxdhDeploymentTranscript.candidateOf codec raw
    | _ => none

/-- One public report batch at every generated position for each candidate in turn. -/
def announceAll (count : Nat) : List Phase1Candidate → OracleComp ProtocolSpec Unit
  | [] => pure ()
  | candidate :: rest => do
      PqxdhRegistrationJointRawReports.batch (List.range count) candidate
      announceAll count rest

/-- The final transcript of a report outcome of the compiled program, empty when the Server constructor failed. -/
def finalTranscript (output : (Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK ((X × Ledger) × Local)) ×
    PqxdhRegistrationJointIdentityCompiler.Local KemSK A) × PqxdhRegistrationJointIdentityRouting.Registry) :
    List Entry :=
  (output.1.1.map fun outcome => outcome.2.1.1.2.transcript).getD []

/-- The A2 report client: the report-instrumented initialized execution of the compiled program of the deployment adversary, which reports every successful accept at the moment it returns, followed by one terminal public batch for the raw candidate of every successful accept of the final transcript. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A) :
    OracleComp ProtocolSpec ((Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK ((X × Ledger) × Local)) ×
      PqxdhRegistrationJointIdentityCompiler.Local KemSK A) × PqxdhRegistrationJointIdentityRouting.Registry) := do
  let output ← PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
    (compileFull setup codec route bounds mode adversary) runtime
  announceAll count (acceptedCandidates codec (finalTranscript output))
  pure output

/-- The ordinary joint-use weak-EUF reduction at generated position `target` built from the A2 report client. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (target : Fin (count + 1)) :=
  PqxdhJointIdentityFreshness.globalReduction setup.joint target ordinaryFallback
    (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
      (PqxdhDynamicIdentityReports.reportExtractor setup.joint (count + 1) fallback
        (PqxdhJointPhase1Reports.routedClient setup.joint (count + 1)
          (client setup codec checks route ensureInit bounds mode adversary (count + 1) runtime))))

/-- Public report batches issue no identity request of any source class. -/
theorem announceAll_bound (count : Nat) (candidates : List Phase1Candidate)
    (predicate : PqxdhDynamicIdentityPool.DynamicSpec.Domain → Prop) [DecidablePred predicate] :
    (announceAll count candidates).IsQueryBoundP (SourceClass predicate) 0 := by
  have batchFree : ∀ (indices : List Nat) (candidate : Phase1Candidate),
      (PqxdhRegistrationJointRawReports.batch indices candidate : OracleComp ProtocolSpec Unit).IsQueryBoundP
        (SourceClass predicate) 0 := by
    intro indices candidate
    induction indices with
    | nil => trivial
    | cons index rest ih =>
        simp only [PqxdhRegistrationJointRawReports.batch, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [SourceClass]), fun _ => by simpa [SourceClass] using ih⟩
  induction candidates with
  | nil => trivial
  | cons candidate rest ih =>
      exact isQueryBoundP_bind (m := 0) (n := 0) (batchFree _ candidate) fun _ _ => ih

/-- The A2 report client creates at most one identity for the generated Server seed plus the transported creation cap. -/
theorem client_creates (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (count : Nat) (runtime : A) :
    (client setup codec checks route ensureInit bounds mode adversary count runtime).IsQueryBoundP
      (SourceClass PqxdhDynamicIdentityPool.IsCreate) (1 + budget.create) := by
  have creates := PqxdhRegistrationJointReportCosts.initialized_creates setup codec checks ensureInit none count
    (compileFull setup codec route bounds mode adversary) runtime
    (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
  have total := isQueryBoundP_bind (ob := fun output => do
      announceAll count (acceptedCandidates codec (finalTranscript output))
      pure output) (m := 0) creates fun output _ =>
    isQueryBoundP_bind (m := 0) (n := 0)
      (announceAll_bound count (acceptedCandidates codec (finalTranscript output)) PqxdhDynamicIdentityPool.IsCreate)
      fun _ _ => isQueryBoundP_pure (SourceClass PqxdhDynamicIdentityPool.IsCreate) output 0
  simpa [client, PqxdhDeploymentCompileCaps.transported] using total

/-- The report run of the A2 client is the report run of the report-instrumented initialized compiled program, followed by the terminal batches from the reached report state. -/
theorem client_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A) :
    PqxdhJointPhase1Reports.run setup.joint count (client setup codec checks route ensureInit bounds mode adversary count
      runtime) =
      PqxdhJointPhase1Reports.run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec checks
        ensureInit none count (compileFull setup codec route bounds mode adversary) runtime) >>= fun reached =>
        (fun after => (reached.1, after.2)) <$> (simulateQ (sourceImpl setup.joint count)
          (announceAll count (acceptedCandidates codec (finalTranscript reached.1)))).run reached.2 := by
  simp only [PqxdhJointPhase1Reports.run, client, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    map_eq_bind_pure_comp, Function.comp_def]

/-- Transfer to the A2 client: an event of the report-instrumented initialized compiled program whose every outcome keeps the report flag raised through the terminal batches has probability at most that of the raised flag in the A2 client's report run. -/
theorem client_transfer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A)
    (event : ReportResult KemSK A ((X × Ledger) × Local) count → Prop)
    (detected : ∀ reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
          (compileFull setup codec route bounds mode adversary) runtime)), event reached →
      ∀ after ∈ support ((simulateQ (sourceImpl setup.joint count)
        (announceAll count (acceptedCandidates codec (finalTranscript reached.1)))).run reached.2),
        after.2.1.occurred = true) :
    letI := Classical.propDecidable
    𝒟[(fun reached => decide (event reached)) <$> PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
          (compileFull setup codec route bounds mode adversary) runtime)] {true} ≤
      𝒟[(fun final => final.2.1.occurred) <$> PqxdhJointPhase1Reports.run setup.joint count
        (client setup codec checks route ensureInit bounds mode adversary count runtime)] {true} := by
  classical
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput,
    client_run]
  have bounded := probEvent_bind_mono
    (mx := PqxdhJointPhase1Reports.run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec
      checks ensureInit none count (compileFull setup codec route bounds mode adversary) runtime))
    (my := fun reached => (pure (decide (event reached)) : ProbComp Bool))
    (oc := fun reached => (fun after => after.2.1.occurred) <$> (simulateQ (sourceImpl setup.joint count)
      (announceAll count (acceptedCandidates codec (finalTranscript reached.1)))).run reached.2)
    (q := fun value : Bool => value = true) (fun reached member => ?_)
  · simpa only [map_bind, Functor.map_map, bind_pure_comp] using bounded
  · by_cases happened : event reached
    · simp only [probEvent_pure, decide_eq_true_eq, happened, ite_true]
      apply le_of_eq
      symm
      apply probEvent_eq_one
      constructor
      · simp
      · intro value supported
        rw [support_map] at supported
        obtain ⟨after, afterMember, rfl⟩ := supported
        exact detected reached member happened after afterMember
    · simp [happened]

/-- Theorem CE-A2 (signing-history form, all accepts, no selection factor). For a deployment adversary in either mode that respects its budget, in the report-instrumented initialized execution of its compiled program with a generated Server seed, the probability that the run passes through a successful raw accept, at any position, whose verified identity key is that of a generated Beacon owner unrevealed at that accept and whose verified key tuple is not among that owner's chronological signing attempts before the accept is at most the sum over the `qCreate + 1` generated identity positions of the ordinary joint-use weak-EUF advantages of the A2 client's reductions, with coefficient one. There is no accept-position, owner, field or report-position factor and no collision term; the premises are the attached-signature format rule `shortRejects` with `setup.wiring` and the adversary's budget. -/
theorem a2_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (NativeForgery setup codec checks ensureInit none (budget.create + 1)
        (compileFull setup codec route bounds mode adversary) runtime final)) <$>
      PqxdhJointPhase1Reports.run setup.joint (budget.create + 1)
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none (budget.create + 1)
          (compileFull setup codec route bounds mode adversary) runtime)] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime fallback
          ordinaryFallback target) := by
  classical
  refine le_trans (client_transfer setup codec checks route ensureInit bounds mode adversary (budget.create + 1) runtime
    _ fun reached _ forgery after afterMember => PqxdhDeploymentAcceptDetection.run_sticky setup.joint _ _ reached.2
      (PqxdhDeploymentAcceptDetection.forgery_detected setup codec checks shortRejects ensureInit none _ _ runtime
        reached forgery) after afterMember) ?_
  have creates := client_creates setup codec checks route ensureInit bounds mode adversary budget respects
    (budget.create + 1) runtime
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint budget.create _ fallback ordinaryFallback
    (creates.mono (by omega))

/-- The report-instrumented initialized execution of the compiled program is an execution of the common deployment experiment: projected to the constructed Server's public data, the adversary's output and the whole ledger (transcript, test session and fresh messages), it has exactly the distribution of the experiment with a generated Server seed, in either mode. The report instrumentation and the private pools add analysis state only. -/
theorem report_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A) :
    (fun reached => (sourceResult reached).1.map fun outcome => (outcome.1, outcome.2.1.1.1, outcome.2.1.1.2)) <$>
        PqxdhJointPhase1Reports.run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec
          checks ensureInit none count (compileFull setup codec route bounds mode adversary) runtime) =
      (fun outcome => outcome.1.map fun result => (result.1, result.2.1, result.2.2.1)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime := by
  have reported := PqxdhRegistrationJointReportSource.initialized_source setup codec checks ensureInit none count
    (compileFull setup codec route bounds mode adversary) runtime
  have compiled := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2
    bounds mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  have projected := congrArg (fun work => (fun result =>
    result.1.map fun outcome => (outcome.1, outcome.2.1.1.1, outcome.2.1.1.2)) <$> work) reported
  have gamed := congrArg (fun work => (fun outcome =>
    outcome.1.map fun result => (result.1, result.2.1, result.2.2.1)) <$> work) compiled
  simp only [Functor.map_map] at projected gamed
  simp only [PqxdhRegistrationJointInitializedReports.sourceResult]
  rw [projected]
  simp only [PqxdhDynamicIdentityPool.initialState, List.length_nil] at gamed
  rw [← gamed]
  congr 1
  funext result
  rcases result with ⟨_ | outcome, after⟩ <;> rfl

end BeaconcryptCore.Computational.PqxdhDeploymentProvenance

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.announceAll_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.announceAll_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_creates

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_transfer

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.report_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.report_game
