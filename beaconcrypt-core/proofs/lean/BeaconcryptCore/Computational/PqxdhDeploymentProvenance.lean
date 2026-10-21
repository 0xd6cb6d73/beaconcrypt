-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection
import BeaconcryptCore.Computational.PqxdhDeploymentReplay
import BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps

/-! Phase 1 provenance in the common deployment experiment (CE-7, CE-A2, signing-history form). The probability space is the report-instrumented initialized execution of the compiled program of a deployment adversary, with a generated Server seed. Under the approved codec laws `Phase1ReadBack` and `Phase2ReadBack`, which it needs through `compile_full_source`, `report_game` shows that, projected to the constructed Server's public data, the adversary's output and the whole ledger, this execution is exactly the deployment experiment with Server identity index 0 in either mode, so the report instrumentation, the private identity and KEM pools and their signing log are analysis state only; the bounds below themselves use no codec law, and the two laws are needed only to read them as statements about the deployment experiment. Every successful accept is reported at the moment it returns, at every generated identity position. The A2 client (`client`) runs this execution and then one terminal public batch for the raw candidate of every successful accept of the final transcript; the terminal batches serve the published-tuple corollaries and add no request of any source class (`announceAll_bound`, `client_creates`, `client_class_bound`). `a2_bound` is CE-A2 over all accepts: the probability that the run passes through a successful raw accept whose verified identity key is a generated Beacon owner's, unrevealed at that accept, and whose verified key tuple is not among that owner's chronological signing attempts before the accept, is at most the sum over the `qCreate + 1` generated identity positions of the ordinary joint-use weak-EUF advantages of the A2 client's reductions, with coefficient one; there is no accept-position, owner, field or report-position factor and no collision term. The event is `PqxdhDeploymentAcceptDetection.NativeForgery` of the compiled program; the bound goes through `forgery_detected`, the sticky report flag (`client_transfer`) and `fieldOrigin_advantage_le_sum`. The premises are the attached-signature format rule `shortRejects` with `setup.wiring` and the adversary's budget, which bounds identity creation by `qCreate` plus the generated Server seed. The unrevealed qualifier is discharged in the deployment: the compiled program stopped after any accept issues no identity-field or KEM-field read (`upto_unread`, from `compile_full_unread`), so no identity is revealed on any stopped run (`stopped_unrevealed`, through `PqxdhDeploymentQuiet.quiet_initialized`), the event without the qualifier (`GeneratedForgery`) is the same event (`generated_forgery_iff`), and `a2_generated_bound` states CE-A2 for every generated owner with the same bound. The query bills of the reductions, which CE-A2pub and CE-R1' share, have the form of the accept/KEM join's T5b: at most `3 * qBundle` signing and `qFinish + qAccept` converted-DH requests per reduction (`a2_service_bound`), the client uniform bill `total caps qInit (transported bounds budget)` (`a2_client_uniform`), `32 * count` further uniform queries per reduction (`a2_reduction_uniform`) and `32 * (count + 1)` plus the client bill for each endpoint game (`a2_game_uniform`), collected in `a2_bills`. -/
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

/-- The A2 client keeps every source-class cap of the initialized compiled program: removing the report instrumentation recovers that program, and the terminal batches issue no request of any source class. -/
theorem client_class_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (count : Nat) (runtime : A)
    (predicate : PqxdhDynamicIdentityPool.DynamicSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (bounded : (PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit none
      (compileFull setup codec route bounds mode adversary) runtime).IsQueryBoundP predicate bound) :
    (client setup codec checks route ensureInit bounds mode adversary count runtime).IsQueryBoundP
      (SourceClass predicate) bound := by
  have erased : (simulateQ PqxdhRegistrationJointReportLift.erase
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
        (compileFull setup codec route bounds mode adversary) runtime)).IsQueryBoundP predicate bound := by
    rw [PqxdhRegistrationJointReportCompiler.initialized_erase]
    exact bounded
  have lifted := (PqxdhRegistrationJointReportCosts.erase_bound predicate _ bound).mp erased
  have reported : (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
      (compileFull setup codec route bounds mode adversary) runtime).IsQueryBoundP (SourceClass predicate) bound :=
    (isQueryBoundP_congr_pred (fun query => by cases query <;> rfl)).mp lifted
  have total := isQueryBoundP_bind (ob := fun output => do
      announceAll count (acceptedCandidates codec (finalTranscript output))
      pure output) (m := 0) reported fun output _ =>
    isQueryBoundP_bind (m := 0) (n := 0)
      (announceAll_bound count (acceptedCandidates codec (finalTranscript output)) predicate)
      fun _ _ => isQueryBoundP_pure (SourceClass predicate) output 0
  simpa [client] using total

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
  rw [client_run]
  have bounded := prEvent_bind_mono_of_forall_le_of_support
    (PqxdhJointPhase1Reports.run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec
      checks ensureInit none count (compileFull setup codec route bounds mode adversary) runtime))
    (fun reached => (pure (decide (event reached)) : ProbComp Bool))
    (fun reached => (fun after => after.2.1.occurred) <$> (simulateQ (sourceImpl setup.joint count)
      (announceAll count (acceptedCandidates codec (finalTranscript reached.1)))).run reached.2)
    (fun value : Bool => value = true) (fun value : Bool => value = true) (fun reached member => ?_)
  · rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton] at bounded
    simpa only [map_bind, Functor.map_map, bind_pure_comp] using bounded
  · by_cases happened : event reached
    · simp only [prEvent_pure, decide_eq_true_eq, happened, ite_true]
      apply le_of_eq
      symm
      apply OracleComp.prEvent_eq_one_of_forall_mem_support
      intro value supported
      rw [support_map] at supported
      obtain ⟨after, afterMember, rfl⟩ := supported
      exact detected reached member happened after afterMember
    · simp only [prEvent_pure, decide_eq_true_eq, happened, ite_false, zero_le]

/-- Theorem CE-A2 (signing-history form, all accepts, no selection factor). For a deployment adversary in either mode that respects its budget, in the report-instrumented initialized execution of its compiled program with a generated Server seed, the probability that the run passes through a successful raw accept, at any position, whose verified identity key is that of a generated Beacon owner unrevealed at that accept and whose verified key tuple is not among that owner's chronological signing attempts before the accept is at most the sum over the `qCreate + 1` generated identity positions of the ordinary joint-use weak-EUF advantages of the A2 client's reductions, with coefficient one. There is no accept-position, owner, field or report-position factor and no collision term; the premises are the attached-signature format rule `shortRejects` with `setup.wiring` and the adversary's budget, and no codec law is used. Reading the bound as a statement about the deployment experiment uses `report_game`, which needs the approved codec laws `Phase1ReadBack` and `Phase2ReadBack`. The unrevealed qualifier holds on every run of the compiled program (`generated_forgery_iff`, `a2_generated_bound`), and the query bills of the reductions are `a2_bills`. -/
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
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint budget.create _ fallback ordinaryFallback
    (creates.mono (by omega))

/-- The compiled program stopped right after its raw accept at any position issues no identity-field, KEM-field, prekey or one-time read, for every adversary and without a budget: the scan keeps the compiled program's zero caps (`compile_full_unread`) and the stopping step issues only the accept command. -/
theorem upto_unread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (index : Nat) (field : Fin 5) (notKernel : field ≠ 4) :
    (PqxdhDeploymentAcceptDetection.upto (compileFull setup codec route bounds mode adversary) index).IsQueryBoundP
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inr field) 0 := by
  refine isQueryBoundP_bind (m := 0) (n := 0) (PqxdhRegistrationJointAcceptCut.scan_bound _ index _ 0
    (PqxdhDeploymentCompileSecrecy.compile_full_unread setup codec route bounds mode adversary field notKernel)) ?_
  intro cut _
  cases cut with
  | complete result => exact isQueryBoundP_pure _ _ 0
  | pending raw next =>
      simp only [PqxdhDeploymentAcceptDetection.stepAccept]
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      intro kind
      simp [PqxdhRegistrationJointRevealCosts.sourceKind] at kind

/-- No identity is revealed on any stopped run of the compiled program: on every outcome of the report run of the compiled program stopped right after its raw accept at any position, `revealedAt` is false for every identity index. The stopped program issues no identity or KEM read (`upto_unread`), so its source execution keeps the private pools quiet (`PqxdhDeploymentQuiet.quiet_initialized`). -/
theorem stopped_unrevealed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (count : Nat) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (index : Nat)
    (runtime : A)
    (stopped : ReportResult KemSK A (PqxdhDeploymentAcceptDetection.Stop KemSK ((X × Ledger) × Local)) count)
    (supported : stopped ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (PqxdhDeploymentAcceptDetection.upto (compileFull setup codec route bounds mode adversary) index) runtime)))
    (identityIndex : Nat) :
    PqxdhRegistrationJointRoutedReveals.revealedAt identityIndex (sourceResult stopped).2.1.1.transcript = false := by
  obtain ⟨original, member, same⟩ := PqxdhRegistrationJointInitializedReports.source_witness setup codec checks
    ensureInit supplied count _ runtime stopped supported
  have quiet := PqxdhDeploymentQuiet.quiet_initialized setup codec checks ensureInit supplied _
    (upto_unread setup codec route bounds mode adversary index 0 (by decide))
    (upto_unread setup codec route bounds mode adversary index 1 (by decide)) _ PqxdhDeploymentQuiet.quiet_empty
    original member
  rw [← same]
  exact PqxdhDeploymentQuiet.unrevealed_of_quiet _ quiet identityIndex

/-- Native origin failure at the selected accept for a generated owner, revealed or not: `PqxdhDeploymentAcceptDetection.ViolationAt` without the conjunct that the owner is unrevealed at the accept. -/
def GeneratedViolation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {Y : Type}
    {count : Nat} (stopped : ReportResult KemSK A (PqxdhDeploymentAcceptDetection.Stop KemSK Y) count) : Prop :=
  ∃ (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (PqxdhDeploymentAcceptDetection.Stop KemSK Y))
    (raw : Pqxdh.Bytes) (session : Nat)
    (next : Option Nat → OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Y)
    (value : PqxdhServerRootPreparation.Verified Reader) (address : Nat)
    (owner : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (target : Fin count) (publicKey : PublicIdentity),
    (sourceResult stopped).1 = some encoded ∧ encoded.2.1 = .accepted raw (some session) next ∧
    PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
    encoded.2.2.owners[address]? = some owner ∧
    stopped.1.2.refs[owner.1]? = some (.generated target.val) ∧
    sourceKeys setup.joint (sourceResult stopped).2.1.1.seeds owner.1 = some publicKey ∧
    value.identity = publicKey.ed25519 ∧
    ¬PqxdhRegistrationJointAttemptDecoding.Occurred value.keys
      (PqxdhRegistrationJointSigningTranscript.messagesAt owner.1 (sourceResult stopped).2.1.1.transcript)

/-- The CE-A2 event without the reveal qualifier: the run passes through some raw accept whose stopped outcome is a `GeneratedViolation`, and continues from it to the final outcome. -/
def GeneratedForgery (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat) {Y : Type}
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Y) (runtime : A)
    (final : ReportResult KemSK A Y count) : Prop :=
  ∃ (index : Nat) (stopped : ReportResult KemSK A (PqxdhDeploymentAcceptDetection.Stop KemSK Y) count),
    stopped ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (PqxdhDeploymentAcceptDetection.upto work index) runtime)) ∧
    final ∈ support (PqxdhRegistrationJointAcceptCutReports.continuation setup codec checks ensureInit count
      PqxdhDeploymentAcceptDetection.resumeStop stopped) ∧
    GeneratedViolation setup codec checks stopped

/-- The reveal qualifier of CE-A2 is vacuous in the deployment experiment: for the compiled program of every adversary in either mode, the CE-A2 event `NativeForgery` and the event `GeneratedForgery` without the unrevealed conjunct are the same set of final outcomes, because no identity is revealed on any stopped run (`stopped_unrevealed`). -/
theorem generated_forgery_iff (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (count : Nat) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (final : ReportResult KemSK A ((X × Ledger) × Local) count) :
    GeneratedForgery setup codec checks ensureInit supplied count (compileFull setup codec route bounds mode adversary)
        runtime final ↔
      NativeForgery setup codec checks ensureInit supplied count (compileFull setup codec route bounds mode adversary)
        runtime final := by
  constructor
  · rintro ⟨index, stopped, member, continued, encoded, raw, session, next, value, address, owner, target, publicKey,
      finished, recorded, attached, found, generated, key, identity, absent⟩
    exact ⟨index, stopped, member, continued, encoded, raw, session, next, value, address, owner, target, publicKey,
      finished, recorded, attached, found, generated, key, identity,
      stopped_unrevealed setup codec checks route ensureInit supplied count bounds mode adversary index runtime stopped
        member owner.1, absent⟩
  · rintro ⟨index, stopped, member, continued, encoded, raw, session, next, value, address, owner, target, publicKey,
      finished, recorded, attached, found, generated, key, identity, _, absent⟩
    exact ⟨index, stopped, member, continued, encoded, raw, session, next, value, address, owner, target, publicKey,
      finished, recorded, attached, found, generated, key, identity, absent⟩

/-- Theorem CE-A2 for every generated owner. With the premises of `a2_bound`, the probability that the run passes through a successful raw accept, at any position, whose verified identity key is that of a generated Beacon owner and whose verified key tuple is not among that owner's chronological signing attempts before the accept, with no condition on reveals, is at most the same sum over the `qCreate + 1` generated identity positions as `a2_bound`. The event is `NativeForgery` without its unrevealed conjunct (`generated_forgery_iff`), so this is at least as strong as `a2_bound`. -/
theorem a2_generated_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (GeneratedForgery setup codec checks ensureInit none (budget.create + 1)
        (compileFull setup codec route bounds mode adversary) runtime final)) <$>
      PqxdhJointPhase1Reports.run setup.joint (budget.create + 1)
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none (budget.create + 1)
          (compileFull setup codec route bounds mode adversary) runtime)] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime fallback
          ordinaryFallback target) := by
  classical
  have same : ∀ final, GeneratedForgery setup codec checks ensureInit none (budget.create + 1)
      (compileFull setup codec route bounds mode adversary) runtime final =
      NativeForgery setup codec checks ensureInit none (budget.create + 1)
        (compileFull setup codec route bounds mode adversary) runtime final := fun final =>
    propext (generated_forgery_iff setup codec checks route ensureInit none (budget.create + 1) bounds mode adversary runtime
      final)
  simp only [same]
  exact a2_bound setup codec checks shortRejects route ensureInit bounds mode adversary budget respects runtime fallback
    ordinaryFallback

/-- The report-instrumented initialized execution of the compiled program is an execution of the common deployment experiment, under the approved codec laws `Phase1ReadBack` and `Phase2ReadBack`, which `compile_full_source` needs: projected to the constructed Server's public data, the adversary's output and the whole ledger (transcript, test session and fresh messages), it has exactly the distribution of the experiment with a generated Server seed and Server identity index 0, in either mode. The index is 0 because `compile_full_source` gives the game the number of identity seeds in the pool at which the instrumented execution starts, and that pool is empty. The report instrumentation and the private pools add analysis state only. -/
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

/-- Query bill of the A2 reductions (signing and static DH, the T5b form). Each reduction of the A2 client, for every generated position and every challenger public identity, makes at most `3 * qBundle` signing requests and at most `qFinish + qAccept` converted-DH requests. These reductions are the ones of CE-A2, CE-A2pub and CE-R1'. -/
theorem a2_service_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (count : Nat) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (target : Fin (count + 1)) (jointPublic : PublicIdentity)
    (signing : Bool) :
    (reduction setup codec checks route ensureInit bounds mode adversary count runtime fallback ordinaryFallback target
      jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass (if signing then .sign else .staticDh))
      (if signing then 3 * budget.bundle else budget.finish + budget.accept) := by
  have source := PqxdhRegistrationJointIdentityCosts.initialized_private setup codec checks ensureInit none
    (compileFull setup codec route bounds mode adversary) runtime (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
    (if signing then .signing else .staticDh) (by cases signing <;> decide)
  have bounded := PqxdhJointPhase1Reports.fieldReduction_query_bound setup.joint count target fallback ordinaryFallback
    (client setup codec checks route ensureInit bounds mode adversary (count + 1) runtime)
    (if signing then .sign else .staticDh) _
    ((isQueryBoundP_congr_pred (PqxdhRegistrationJointReportedAuthentication.service_class signing)).mp
      (client_class_bound setup codec checks route ensureInit bounds mode adversary (count + 1) runtime _ _ source))
    jointPublic
  cases signing <;> simpa [PqxdhRegistrationJointOpenCosts.privateTotal, PqxdhDeploymentCompileCaps.transported,
    reduction] using bounded

/-- Uniform bill of the A2 client: under the existing uniform-bill premises (`initBound`, `KemBound setup caps`), the A2 client pays at most the complete all-reply uniform bill of the compiled program at its transported caps; the terminal batches add no uniform query. -/
theorem a2_client_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (count : Nat) (runtime : A) :
    (client setup codec checks route ensureInit bounds mode adversary count runtime).IsQueryBoundP
      (SourceClass (PqxdhDynamicIdentityRouting.dynamicClass
        (PqxdhJointIdentityFamily.IsClass PqxdhJointIdentityFamily.Kind.uniform)))
      (PqxdhRegistrationJointIdentityUniform.total caps qInit (PqxdhDeploymentCompileCaps.transported bounds budget)) := by
  have original := PqxdhRegistrationJointIdentityUniform.initialized setup codec checks ensureInit qInit initBound caps
    kemBound none (compileFull setup codec route bounds mode adversary) runtime
    (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
  exact client_class_bound setup codec checks route ensureInit bounds mode adversary count runtime _ _
    ((isQueryBoundP_congr_pred PqxdhRegistrationJointNativeOriginUniform.uniform_class).mp original)

/-- Uniform bill of each A2 reduction: the other `count` reserved identity seeds plus the A2 client's uniform bill, for every challenger public identity. -/
theorem a2_reduction_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (count : Nat) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (target : Fin (count + 1)) (jointPublic : PublicIdentity) :
    (reduction setup codec checks route ensureInit bounds mode adversary count runtime fallback ordinaryFallback target
      jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .uniform)
      (32 * count + PqxdhRegistrationJointIdentityUniform.total caps qInit
        (PqxdhDeploymentCompileCaps.transported bounds budget)) :=
  PqxdhJointPhase1Reports.fieldReduction_query_bound setup.joint count target fallback ordinaryFallback
    (client setup codec checks route ensureInit bounds mode adversary (count + 1) runtime) .uniform _
    (a2_client_uniform setup codec checks route ensureInit qInit initBound caps kemBound bounds mode adversary budget
      respects (count + 1) runtime) jointPublic

/-- Total query bill of each ordinary joint-use weak-EUF game of an A2 reduction: the game also samples its own target seed, so all `count + 1` reserved seeds plus the A2 client's uniform bill are paid. -/
theorem a2_game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (count : Nat) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (target : Fin (count + 1)) :
    (PqxdhJointIdentity.game setup.joint (reduction setup codec checks route ensureInit bounds mode adversary count
      runtime fallback ordinaryFallback target)).IsTotalQueryBound
      (32 * (count + 1) + PqxdhRegistrationJointIdentityUniform.total caps qInit
        (PqxdhDeploymentCompileCaps.transported bounds budget)) :=
  PqxdhJointPhase1Reports.fieldReductionGame_uniform_bound setup.joint count target fallback ordinaryFallback
    (client setup codec checks route ensureInit bounds mode adversary (count + 1) runtime) _
    (a2_client_uniform setup codec checks route ensureInit qInit initBound caps kemBound bounds mode adversary budget
      respects (count + 1) runtime)

/-- The query bills of the A2 reductions, collected as in the accept/KEM join's T5b: for the reductions of `a2_bound`, `a2_generated_bound`, CE-A2pub and CE-R1' (count `qCreate`), every reduction makes at most `3 * qBundle` signing, `qFinish + qAccept` converted-DH and `32 * qCreate + total caps qInit (transported bounds budget)` uniform requests for every challenger public identity, and each endpoint game makes at most `32 * (qCreate + 1) + total caps qInit (transported bounds budget)` queries in total. -/
theorem a2_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (target : Fin (budget.create + 1)) :
    (∀ jointPublic : PublicIdentity,
      (reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime fallback
        ordinaryFallback target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .sign)
        (3 * budget.bundle) ∧
      (reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime fallback
        ordinaryFallback target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .staticDh)
        (budget.finish + budget.accept) ∧
      (reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime fallback
        ordinaryFallback target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .uniform)
        (32 * budget.create + PqxdhRegistrationJointIdentityUniform.total caps qInit
          (PqxdhDeploymentCompileCaps.transported bounds budget))) ∧
    (PqxdhJointIdentity.game setup.joint (reduction setup codec checks route ensureInit bounds mode adversary
      budget.create runtime fallback ordinaryFallback target)).IsTotalQueryBound
      (32 * (budget.create + 1) + PqxdhRegistrationJointIdentityUniform.total caps qInit
        (PqxdhDeploymentCompileCaps.transported bounds budget)) := by
  refine ⟨fun jointPublic => ⟨?_, ?_, a2_reduction_uniform setup codec checks route ensureInit qInit initBound caps
    kemBound bounds mode adversary budget respects budget.create runtime fallback ordinaryFallback target jointPublic⟩,
    a2_game_uniform setup codec checks route ensureInit qInit initBound caps kemBound bounds mode adversary budget
      respects budget.create runtime fallback ordinaryFallback target⟩
  · simpa using a2_service_bound setup codec checks route ensureInit bounds mode adversary budget respects
      budget.create runtime fallback ordinaryFallback target jointPublic true
  · simpa using a2_service_bound setup codec checks route ensureInit bounds mode adversary budget respects
      budget.create runtime fallback ordinaryFallback target jointPublic false

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

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.client_class_bound

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

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.upto_unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.upto_unread

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.stopped_unrevealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.stopped_unrevealed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.generated_forgery_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.generated_forgery_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_generated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_generated_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.report_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.report_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_service_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_service_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_client_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_reduction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_reduction_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_game_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProvenance.a2_bills
