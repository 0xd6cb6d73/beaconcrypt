-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTrace
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills

/-! LQ-F: the per-target KEM transfer of the common deployment experiment (CE-9, plan section 9 steps 9.1-9.4) carried to the LQ-F later game, for confidentiality only. A deployment event reads the post-run adversary's output, the secrecy ledger (transcript, test session with the hidden bit, fresh messages) and the produced frames (`Observed`, `observeCompiled`, `observeGame`); a claim names a record handle, and its target is the budgeted public designation of that handle on the run's transcript, a pair `g = (i, k)` of raw-accept ordinal and KEM creation index, exactly as in CE-9 (`PqxdhDeploymentKemTransfer.target`). Step 9.1 (`eligible_server`) is an equality: the LQ-F game's probability of the event with target `g` equals the probability of T4's event `Decided ∧ GoodKem k ∧ KeyMatchFinal k` in the logged annotated initialized execution of the tagged compiled LQ-F program at ordinal `i`, with the log forgotten. Its proof is CE-9's with the logged source: CE-COMPILE for the LQ-F game (`LaterServerCompile.compile_server_source`), the logged trace and its run invariant (`LaterServerTrace.compiled_server_trace`, `traced_source`, `tag_traced`), which give the key match at the designated target (`keymatch_server`), and GoodKem for programs with no KEM read (`LaterServerTrace.goodKem_later`). Steps 9.2-9.4 (`kem_transfer_server`) chain T4, the generic KEM hop and T6 for the logged source (`LaterServerOpaque.transfer`) with the creation cap of the compiled program (`LaterServerCompileBudget.compile_server_creates`): per target, one ordinary one-key ML-KEM IND-CCA advantage of the exact proof-carrying adversary at the logged exposure and one ML-KEM correctness error, each with coefficient one, and the logged opaque KEM-ideal branch of the per-target decision remains. `kem_transfer_server_bills` instantiates `LaterServerBills.adversary_bound` at the transported caps of the compiled LQ-F program with its single Server read, and `kem_transfer_server_sum` is the exact-sum headline over all targets through `UniformTargetSelection.split`. The event may depend on the post-run reveal, which holds the Server's identity seed and ephemeral scalars and every Beacon secret of the profile; the transfer uses no DH secrecy, no Gap-DH and no EUF assumption, only ML-KEM, so it survives the reveal, and no authentication statement is made. Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`, `FunctionalDecapsulation` (the premise of the KEM hop) and the run-phase budget; the bills also take the existing cost premises `KemBound setup caps` and `initBound` and the post-run budget. T4 is one-sided, so a two-sided transfer needs CE-9b. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Entry Handle FullSpec ModeSpec Mode Budget FreshBounds asModeO)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentLater (Snap PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhDeploymentLaterServerCompile (compileServer mergeServer)
open PqxdhDeploymentLaterServerCompileBudget (laterTransported)
open PqxdhDeploymentKemTransfer (Observed target selectedKem regOf registrations)
open PqxdhDeploymentRegistrationTrace (Logged acceptsOf)
open PqxdhDeploymentLaterServerTrace (traceFrom)
open PqxdhDeploymentLaterServerCommands (tag)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- The observation of a result of the compiled LQ-F program: the post-run adversary's output, the ledger and the produced frames. -/
def observeCompiled (result : Out × (Ledger × (Snap × Local))) : Observed Out :=
  (result.1, result.2.1, result.2.2.2.produced)

/-- The observation of an outcome of the LQ-F game, when the Server was constructed. -/
def observeGame (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK)) :
    Option (Observed Out) :=
  outcome.map fun result => (result.2.1, result.2.2.1, result.2.2.2.2.1.produced)

/-- The per-target decision of the compiled LQ-F program: the event holds and the claim designates `g`. It reads only the program's result. -/
noncomputable def decision (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (budget : Budget) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (result : Out × (Ledger × (Snap × Local))) : Bool :=
  event (observeCompiled result) && decide (target crypto codec serverKid budget claim (observeCompiled result) = some g)

/-- The event on an outcome of the LQ-F game: false when no Server was constructed. -/
def happens (event : Observed Out → Bool)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A) : Bool :=
  (observeGame outcome.1).any event

/-- The target designated on an outcome of the LQ-F game. -/
noncomputable def designated (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (budget : Budget) (claim : Observed Out → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A) :
    Option (Fin budget.accept × Fin budget.capacity) :=
  (observeGame outcome.1).bind (target crypto codec serverKid budget claim)

/-- A result of a tagged logged program, without its tag, is a result of the program. -/
theorem tag_support (program : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (index : Nat)
    (outcome : X × PqxdhRegistrationJointAcceptCutTag.Tag) (reached : outcome ∈ support (tag program index)) :
    outcome.1 ∈ support program := by
  rw [← PqxdhDeploymentLaterServerCommands.tag_erase program index, support_map]
  exact ⟨outcome, reached, rfl⟩

/-- Step 9.1 for the LQ-F game, pointwise: in the logged annotated initialized execution of the tagged traced compiled LQ-F program at raw-accept ordinal `i`, from empty pools, every outcome whose per-target decision for `g = (i, k)` holds recorded, at the selected raw accept, bytes that returned session `i`, pass the native verification prefix, and verify to the public key at KEM creation index `k` of the final pool. -/
theorem keymatch_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      (((Out × (Ledger × (Snap × Local))) × List Logged) × PqxdhRegistrationJointAcceptCutTag.Tag) ×
        PqxdhDeploymentLaterServerSource.Log)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (reached : (some outcome, after) ∈ support ((PqxdhDeploymentLaterServerSource.initialized setup codec checks
      ensureInit none (tag (traceFrom (compileServer setup codec route bounds mode first second) []) g.1.val)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (decided : decision setup.source.crypto codec setup.serverKeyId budget event claim g outcome.1.2.1.1.1 = true) :
    ∃ raw value, outcome.1.2.1.2 = some (raw, some g.1.val) ∧
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
      (after.1.2.keys[g.2.val]?).map Prod.fst = some value.keys.pqKey := by
  have tagged := PqxdhDeploymentLaterServerTrace.source_support setup codec checks ensureInit none _ _ _ outcome reached
  have tagEq := PqxdhDeploymentLaterServerTrace.tag_traced _ g.1.val outcome.1.2.1 tagged
  have logEq := PqxdhDeploymentLaterServerTrace.compiled_server_trace setup codec route bounds mode first second
    outcome.1.2.1.1 (tag_support _ g.1.val outcome.1.2.1 tagged)
  have projected : (some ((outcome.1.1, outcome.1.2.1.1, outcome.1.2.2), outcome.2), after) ∈ support
      ((PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none
        (traceFrom (compileServer setup codec route bounds mode first second) [])).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
    rw [← PqxdhDeploymentLaterServerCommands.tag_erase (traceFrom (compileServer setup codec route bounds mode first
      second) []) g.1.val, PqxdhDeploymentLaterServerTrace.source_map, support_map]
    exact ⟨_, reached, rfl⟩
  obtain ⟨traced, poolEq⟩ := PqxdhDeploymentLaterServerTrace.traced_source setup codec checks ensureInit none _ _ rfl
    after ((outcome.1.1, outcome.1.2.1.1, outcome.1.2.2), outcome.2) projected
  simp only at traced poolEq
  simp only [decision, Bool.and_eq_true, decide_eq_true_eq] at decided
  obtain ⟨_, targeted⟩ := decided
  obtain ⟨handle, _, designatedIn⟩ := Option.bind_eq_some_iff.mp targeted
  obtain ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, pqFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys _ codec setup.serverKeyId _ handle _ _
      (PqxdhDeploymentKemTransfer.designateIn_some _ codec setup.serverKeyId budget _ handle g designatedIn)
  have acceptLogged : (raw, some g.1.val) ∈ acceptsOf outcome.1.2.1.1.2 := by
    rw [logEq]
    simp only [acceptsOf, registrations, List.mem_filterMap]
    exact ⟨.accept raw (some g.1.val), ⟨_, PqxdhDeploymentKemTransfer.acceptOf_mem _ _ raw rawFound, rfl⟩, rfl⟩
  obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp acceptLogged
  have samePosition := traced.positional position raw g.1.val positionFound
  rw [← samePosition] at positionFound
  obtain ⟨value, checked⟩ := traced.verified raw g.1.val acceptLogged
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup codec checks raw value checked
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  obtain ⟨bytes, bytesFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  have bundleLogged : Logged.bundle g.2.val (some bytes) ∈ outcome.1.2.1.1.2 := by
    rw [logEq]
    simp only [registrations, List.mem_filterMap]
    exact ⟨_, PqxdhDeploymentKeyMatch.bundleOf_mem _ _ bytes bytesFound, rfl⟩
  obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := traced.bundles g.2.val bytes bundleLogged
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at publishedRead
  subst publishedRead
  rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pqFound
  refine ⟨raw, value, by rw [tagEq, positionFound], checked, ?_⟩
  rw [poolEq, pooled, pqFound]

/-- Step 9.1 for the LQ-F game: for a target `g = (i, k)`, the probability that the LQ-F later game ends with the event and the claim designating `g` equals the probability of T4's event in the logged annotated initialized execution of the tagged compiled LQ-F program at raw-accept ordinal `i`, with the log forgotten: the selected accept returned a session and the per-target decision holds (`Decided`), KEM key `k` was never disclosed (`GoodKem`), and the selected raw bytes verify to the public key at KEM creation index `k` of the final pool (`KeyMatchFinal`). The event reads the post-run adversary's output, the ledger and the produced frames; the approved Phase 1 and Phase 2 read-back contracts are the only premises, and no budget is needed. -/
theorem eligible_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
    (letI := Classical.propDecidable
    𝒟[(fun final => decide (PqxdhRegistrationJointKemRawBridge.Decided
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g) final ∧
        PqxdhRegistrationJointKemRawBridge.GoodKem (selectedKem budget g) final ∧
        PqxdhRegistrationJointKemRawBridge.KeyMatchFinal setup codec checks (selectedKem budget g) final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none
          (tag (compileServer setup codec route bounds mode first second) g.1.val)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}) := by
  set work := compileServer setup codec route bounds mode first second with workEq
  set tagged := tag (traceFrom work []) g.1.val with taggedEq
  set start : PqxdhRegistrationJointServerPrefix.State KemSK A :=
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) with startEq
  have erased : work = (fun outcome => outcome.1.1) <$> tagged := by
    calc work = Prod.fst <$> traceFrom work [] := (PqxdhDeploymentLaterServerTrace.traceFrom_erase work []).symm
      _ = Prod.fst <$> (Prod.fst <$> tagged) := by rw [taggedEq, PqxdhDeploymentLaterServerCommands.tag_erase]
      _ = (fun outcome => outcome.1.1) <$> tagged := by rw [Functor.map_map]
  have retagged : tag work g.1.val = (fun outcome => (outcome.1.1, outcome.2)) <$> tagged := by
    have mapped := PqxdhDeploymentLaterServerTrace.tag_map Prod.fst (traceFrom work []) g.1.val
    rw [PqxdhDeploymentLaterServerTrace.traceFrom_erase] at mapped
    exact mapped
  have leftRun : (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none work).run start =
      (fun result => (result.1.map fun outcome => ((outcome.1.1, outcome.1.2.1.1.1, outcome.1.2.2), outcome.2),
        result.2)) <$> (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none tagged).run
          start := by
    have mapped := PqxdhDeploymentLaterServerTrace.source_map setup codec checks ensureInit none
      (fun outcome : ((Out × (Ledger × (Snap × Local))) × List Logged) × PqxdhRegistrationJointAcceptCutTag.Tag =>
        outcome.1.1) tagged start
    rw [← erased] at mapped
    exact mapped
  have rightRun : (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none
      (tag work g.1.val)).run start =
      (fun result => (result.1.map fun outcome => ((outcome.1.1, (outcome.1.2.1.1.1, outcome.1.2.1.2),
        outcome.1.2.2), outcome.2), result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none tagged).run start := by
    rw [retagged]
    exact PqxdhDeploymentLaterServerTrace.source_map setup codec checks ensureInit none _ tagged start
  have game := PqxdhDeploymentLaterServerCompile.compile_server_source setup codec checks route ensureInit phase1
    phase2 bounds mode first second start
  change _ = (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first
    second).run runtime at game
  rw [← game, leftRun, rightRun]
  simp only [Functor.map_map]
  congr 2
  apply PqxdhDeploymentKemTransfer.map_support_congr
  rintro ⟨_ | outcome, after⟩ member
  · simp [happens, observeGame, mergeServer, PqxdhRegistrationJointKemRawBridge.Decided]
  · have observed : observeGame (mergeServer (some (PqxdhRegistrationJointInitializedSchedule.eraseOutcome
        (outcome.1.1, outcome.1.2.1.1.1, outcome.1.2.2), outcome.2), after.2)).1 =
        some (observeCompiled outcome.1.2.1.1.1) := rfl
    have good : PqxdhRegistrationJointKemRawBridge.GoodKem (selectedKem budget g)
        ((some (outcome.1.1, (outcome.1.2.1.1.1, outcome.1.2.1.2), outcome.1.2.2)).map
          (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), after) := by
      apply PqxdhDeploymentLaterServerTrace.goodKem_later setup codec checks ensureInit none work
        (PqxdhDeploymentLaterServerCompileBudget.compile_server_no_kem setup codec route bounds mode first second)
        g.1.val runtime
      rw [rightRun, Functor.map_map, support_map]
      exact ⟨_, member, rfl⟩
    rw [decide_eq_decide]
    constructor
    · rintro ⟨happened, chosen⟩
      simp only [happens, Option.map_some] at happened
      rw [observed] at happened
      simp only [designated, Option.map_some] at chosen
      rw [observed] at chosen
      have decided : decision setup.source.crypto codec setup.serverKeyId budget event claim g outcome.1.2.1.1.1 =
          true := by
        simp only [decision, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by simpa using happened, by simpa using chosen⟩
      obtain ⟨raw, value, tagEq, checked, keys⟩ := keymatch_server setup codec checks route ensureInit phase1 bounds
        mode first second budget event claim g runtime outcome after member decided
      refine ⟨⟨_, rfl, decided, by simp only [tagEq]; rfl⟩, good, _, raw, some g.1.val, value, rfl, tagEq, checked,
        keys⟩
    · rintro ⟨⟨reached, found, decided, _⟩, _⟩
      simp only [Option.map_some, Option.some.injEq] at found
      subst found
      simp only [decision, Bool.and_eq_true, decide_eq_true_eq] at decided
      refine ⟨?_, ?_⟩
      · simp only [happens, Option.map_some]
        rw [observed]
        exact decided.1
      · simp only [designated, Option.map_some]
        rw [observed, Option.bind_some]
        exact decided.2

/-- Steps 9.2-9.4 for one target `g = (i, k)` of the LQ-F later game, for a run-phase budget-respecting `A₁` and every post-run adversary: the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability that the logged opaque KEM-ideal branch of the compiled LQ-F program accepts the per-target decision, plus one ordinary one-key ML-KEM IND-CCA advantage of the exact proof-carrying adversary at the logged exposure and one ML-KEM correctness error, both with coefficient one. The chain is CE-COMPILE for the LQ-F game with the bundle-to-pool invariant over the logged run (`eligible_server`), T4 for the logged source with the creation cap of the compiled program (`compile_server_creates`), the generic KEM hop and T6 for the logged source (`LaterServerOpaque.transfer`). This is a confidentiality statement: the event may read the post-run adversary's output, which depends on the post-run reveal; no authentication is claimed. -/
theorem kem_transfer_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        false] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
          (PqxdhDeploymentLaterServerCut.scanned setup codec checks
            (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
            (compileServer setup codec route bounds mode first second) g.1.val)
          runtime budget.create (selectedKem budget g)).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  rw [eligible_server setup codec checks route ensureInit phase1 phase2 bounds mode first second budget event claim g
    runtime]
  exact PqxdhDeploymentLaterServerOpaque.transfer setup functional codec checks ensureInit none _ _ runtime
    budget.create (selectedKem budget g) g.1.val
    (IsQueryBoundP.mono (PqxdhDeploymentLaterServerCompileBudget.compile_server_creates setup codec route bounds mode
      first second budget respects) (Nat.le_succ _))

/-- Bills of the per-target KEM reduction for the LQ-F game: `LaterServerBills.adversary_bound` at the transported caps of the compiled LQ-F program, with its single Server read. Prechallenge: `(qInit + 32) + (keygenCost · qCreate + V)` uniform queries, `decapsBase · qFinish` base queries and `qFinish` logical decapsulations; postchallenge: `V`, `decapsBase · qFinish` and `qFinish`; where `V = uniformCap caps qCreate qFinish (OpenUniform.total caps (laterTransported bounds budget post)) qAccept`. The post-run budget enters only the uniform allowance `V`; the Server read costs nothing. -/
theorem kem_transfer_server_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileServer setup codec route bounds mode first second) g.1.val)
        runtime budget.create (selectedKem budget g)).MakesAtMostQueries
      ((qInit + 32) + (caps.keygenCost * budget.create + PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create
        budget.finish (PqxdhRegistrationJointOpenUniform.total caps (laterTransported bounds budget post))
        budget.accept))
      (caps.decapsBase * budget.finish) budget.finish
      (PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create budget.finish
        (PqxdhRegistrationJointOpenUniform.total caps (laterTransported bounds budget post)) budget.accept)
      (caps.decapsBase * budget.finish) budget.finish :=
  PqxdhDeploymentLaterServerBills.adversary_bound setup codec checks caps bounded ensureInit qInit initBound none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileServer setup codec route bounds mode first second) (laterTransported bounds budget post) 1
    (PqxdhDeploymentLaterServerCompileBudget.compile_server_certified setup codec route bounds mode first second budget
      respects post postRespects)
    (PqxdhDeploymentLaterServerCompileBudget.compile_server_reads setup codec route bounds mode first second) runtime
    budget.create (selectedKem budget g) g.1.val

/-- Exact-sum headline of the key transfer for the LQ-F game: the probability that the LQ-F later game ends with the event and a designated claim is at most the sum, over all targets `g` in `Fin qAccept × Fin (qCreate + 1)`, of the logged opaque KEM-ideal branch of `g`'s decision plus one IND-CCA advantage of `g`'s proof-carrying adversary plus one correctness error, each with coefficient one. The first step is the exact split `UniformTargetSelection.split`; no selection factor and no EUF term is charged. -/
theorem kem_transfer_server_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        (designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.capacity,
        (𝒟[PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g)
          g.1.val false] {true} +
        ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
            (PqxdhDeploymentLaterServerCut.scanned setup codec checks
              (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
              (compileServer setup codec route bounds mode first second) g.1.val)
            runtime budget.create (selectedKem budget g)).toINDCCA).toReal +
          PqxdhRegistrationJointKemRawGame.correctnessError setup)) := by
  rw [UniformTargetSelection.split]
  exact Finset.sum_le_sum fun g _ => kem_transfer_server setup functional codec checks route ensureInit phase1 phase2
    bounds mode first second budget respects event claim g runtime

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.tag_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.tag_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.keymatch_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.keymatch_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.eligible_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.eligible_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.kem_transfer_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.kem_transfer_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.kem_transfer_server_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.kem_transfer_server_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.kem_transfer_server_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer.kem_transfer_server_sum
