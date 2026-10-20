-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly
import BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCompile
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots
import BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterLift

/-!
# The per-target chain of the later-quantum CE-12 headlines (CE-12 P3, design.md section 9, design-v2 section 10)

The later-quantum (LQ-F) form of the per-target chain of `PqxdhDeploymentHeadlineChain`, from the LQ-F game `PqxdhDeploymentLaterServerGame.game` (the actual Server constructor with a generated seed, identity index 0, the run phase of `first`, the post-run reveal of the Server seed, the ephemeral log and the Beacon-side secrets, and the post phase of `second`) to the later record lift's ideal worlds. For one target `g = (i, k)`, an event and a claim of the LQ-F observation (the post adversary's output, the run-phase ledger and the produced frames), `D_g` is the event with the claim's budgeted designation equal to `g` (`PqxdhDeploymentLaterServerTransfer.happens`, `designated`), and `dec_g` is the same decision read on a later record-lift view (`PqxdhDeploymentIdealHandoff.decisionOn` on `viewObserved`).

- Losses: `kemLossL` (one IND-CCA advantage of the logged per-target proof-carrying KEM adversary plus the ML-KEM correctness error, `PqxdhDeploymentLaterServerTransfer.kem_transfer_server`) and `slotLossL` (item 2 over the logged source at two slots, `PqxdhDeploymentLaterServerItemTargets.slotLossL` at the transported caps `laterTransported bounds budget post`, whose first term is `(qAccept + qFinish + qHmac + qHmac₂)/2^256`); `recLossL`, the later record-lift loss of `PqxdhRecordLiftLaterLift.later_record_lift` at the ideal environment of the target with the environment's reveal `envReveal` and the post budget (bill input `inputL`).
- C1-C2 (`chain_slot_later`, `chain_slot_later_close`): the LQ-F game's `D_g` against item 2's logged two-slot world `laterSlotGame`, from `kem_transfer_server`, `kem_transfer_server_two_sided` and `later_slots_two`.
- C3 (`chain_ideal_later`, `chain_ideal_later_close`, CE-KT-L's chain): to the later ideal game `IL_g` (`PqxdhDeploymentIdealLaterGame.idealLaterGame`, decision `ceDecideL`) by `PqxdhDeploymentIdealLaterCompile.ideal_compile_server`.
- C3-C5 (`ideal_world_later`, `ideal_world_view_later`, `chain_view_later`, `chain_close_later`): the later `ideal_world`, `ideal_compile_server` composed with `PqxdhDeploymentIdealLaterEnv.c6_idealGame_decide` (the later record world `PqxdhRecordLiftLater.run` with `envGD` and `envReveal`), and its form on the view of the all-real later chain world (`PqxdhRecordLiftLaterWorlds.laterReal_game`).
- C6: `later_real_slots_server` (the Server-side conjuncts `ServerSlots` on every outcome of the later chain world, under `Phase1ReadBack` alone; the Server-side form of `PqxdhDeploymentIdealLaterSlots.later_slots`), `chain_server_later` (with `ServerSlots`, no anomaly term), `later_view_unslotted` (an event without `IdealSlots` on the later view is within the run-phase anomaly of `first`), `chain_slots_later` (with `IdealSlots`, plus the anomaly on the run-phase record world of `first`, `later_view_slots_le`) and `chain_beta_later` (the anomaly bounded by `β_g` of `first`, `PqxdhDeploymentHeadlineAnomaly.anomaly_beta`).
- C7: `records_close_later`, `records_le_later`, the event form of the later record lift at the frame of `PqxdhDeploymentIdealFrame.frame_idealD`.
- The exact split over the tight target domain for an event that names a designated claim (`split_named_later`, from `PqxdhDeploymentLaterTargetRange.split_create_later`).

The anomaly is a run-phase event: it reads only the run-phase transcript, which the post phase does not change (`later_anomaly_eq`), so it is bounded on `first`'s run (`anomaly_le_pk`, then `ptc_bound`). These are compositions of existing theorems; no assumption or contract is added. Later mode claims confidentiality only: no origin, binding or authentication statement is made, and no theorem A2, T5 or T8 is cited on the later compiled program.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed selectedKem)
open PqxdhDeploymentLaterServerTransfer (happens designated decision)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentLaterServerCompile (compileServer)
open PqxdhDeploymentLaterServerCompileBudget (laterTransported)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots Anomaly)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted startupG inputG chance_ne_top)

/-! ### Losses -/

section Losses
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- `kemLossL g d_g` (design.md section 9.1): the IND-CCA advantage of the logged per-target proof-carrying KEM adversary of the decision `d_g(event, claim)` on the compiled LQ-F program (`PqxdhDeploymentLaterServerTransfer.kem_transfer_server`) plus the ML-KEM correctness error, each with coefficient one. -/
noncomputable def kemLossL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) : ℝ :=
  setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
      (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) g.1.val)
      runtime budget.create (selectedKem budget g)).toINDCCA +
    PqxdhRegistrationJointKemRawGame.correctnessError setup

/-- `slotLossL g d_g` (design.md section 9.1, U-L1): item 2 over the logged LQ-F source at two slots for the decision `d_g(event, claim)` (`PqxdhDeploymentLaterServerItemTargets.slotLossL` at the transported caps `laterTransported bounds budget post`): the R1 guessing term `(qAccept + qFinish + qHmac + qHmac₂)/2^256` (`slotLossL_transported`), two HMAC-PRF advantages and the key-schedule bounds of the two hidden entries. -/
noncomputable def slotLossL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) : ℝ :=
  PqxdhDeploymentLaterServerItemTargets.slotLossL (Reader := Reader) setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
    (laterTransported bounds budget post)

/-- The later bill input of the record lift at the ideal environment of a target: `BI_g` (`PqxdhDeploymentHeadlineChain.inputG`) with the post budget. -/
def inputL (caps : KemCaps) (qInit : ℕ) (budget : Budget) (bounds : FreshBounds) (post : PostBudget) :
    PqxdhRecordLiftLaterTargets.LaterBillInput :=
  ⟨inputG caps qInit budget bounds, post⟩

/-- `laterRecLoss_g e` (design.md section 9.1): the later record-lift loss (`PqxdhRecordLiftLaterTargets.laterRecordLoss`) of the explicit later chain, integrity and privacy reductions of `PqxdhRecordLiftLaterLift.later_record_lift` at the ideal environment of the target of `g` with the environment's reveal `envReveal`, for the view event `e`, with zero aliasing and refusal terms. -/
noncomputable def recLossL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget) (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (caps : KemCaps) (qInit : ℕ)
    (event : View 2 (EnvG KemSK budget) Out → Bool) : ℝ≥0∞ :=
  PqxdhRecordLiftLaterTargets.laterRecordLoss setup codec 2 setup.hmac fallback
    (PqxdhRecordLiftLaterChain.laterChainReduction setup codec route setup.serverKeyId bounds 2)
    (PqxdhRecordLiftLaterCtx.laterCtxReduction setup codec route setup.serverKeyId bounds)
    (PqxdhRecordLiftLaterPriv.laterPrivReduction setup codec route setup.serverKeyId bounds)
    PqxdhRecordLiftLaterCtx.laterCtxBills
    PqxdhRecordLiftLaterTargets.laterNoTerm PqxdhRecordLiftLaterTargets.laterNoTerm
    PqxdhRecordLiftLaterTargets.laterNoTerm
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode envReveal
    first second (fun view => pure (event view)) budget post (inputL caps qInit budget bounds post)

end Losses

/-! ### C1-C5: the per-target chain -/

section Chain
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- C1-C2, one-sided: for a run-phase budget-respecting `first`, a post adversary `second` within its post budget and a target `g`, the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability of item 2's logged two-slot world of `g`'s decision plus `kemLossL` and `slotLossL`. -/
theorem chain_slot_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[PqxdhDeploymentLaterServerItemTargets.laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        2] {true} +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g
        runtime) := by
  have kem := PqxdhDeploymentLaterServerTransfer.kem_transfer_server setup functional codec checks route ensureInit
    phase1 phase2 bounds mode first second budget respects event claim g runtime
  have item2 := PqxdhDeploymentLaterServerItemKeys.later_slots_two (Reader := Reader) setup codec route checks correct
    ensureInit bounds mode first second budget respects post postRespects event claim g runtime
  set opq := PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
    false with hopq
  set slot := PqxdhDeploymentLaterServerItemTargets.laterSlotGame (Reader := Reader) setup codec checks ensureInit none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val 2
    with hslot
  have step := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage opq slot
  refine kem.trans ?_
  calc _ ≤ (𝒟[slot] {true} + ENNReal.ofReal (opq.boolDistAdvantage slot)) +
        ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
          runtime) := add_le_add step le_rfl
    _ ≤ _ := by
        rw [add_right_comm]
        exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal item2)

/-- C1-C2, two-sided: the probability that the LQ-F game ends with the event and the claim designating `g` and the probability of item 2's logged two-slot world of `g`'s decision differ by at most `kemLossL + slotLossL`. -/
theorem chain_slot_later_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      (𝒟[PqxdhDeploymentLaterServerItemTargets.laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        2] {true}).toReal| ≤
      kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g runtime +
        slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g runtime := by
  have kem := PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_two_sided setup functional codec checks route
    ensureInit phase1 phase2 bounds mode first second budget respects event claim g runtime
  have item2 := PqxdhDeploymentLaterServerItemKeys.later_slots_two (Reader := Reader) setup codec route checks correct
    ensureInit bounds mode first second budget respects post postRespects event claim g runtime
  exact (abs_sub_le _ _ _).trans (add_le_add kem item2)

/-- C1-C3, one-sided (CE-KT-L's chain): the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability that the later ideal game of `g` (`PqxdhDeploymentIdealLaterGame.idealLaterGame`, item 2's two hidden entries uniform, the real post phase) ends with the same decision (`ceDecideL`), plus `kemLossL` and `slotLossL`. -/
theorem chain_ideal_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run runtime] {true} +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g
        runtime) := by
  rw [← PqxdhDeploymentIdealLaterCompile.ideal_compile_server setup codec route checks phase1 phase2 ensureInit bounds
    mode first second budget respects event claim g runtime]
  exact chain_slot_later setup functional codec checks route ensureInit phase1 phase2 correct bounds mode first second
    budget respects post postRespects event claim g runtime

/-- C1-C3, two-sided (CE-KT-L's chain): the probability that the LQ-F game ends with the event and the claim designating `g` and the probability that the later ideal game of `g` ends with the same decision differ by at most `kemLossL + slotLossL`. -/
theorem chain_ideal_later_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run runtime] {true}).toReal| ≤
      kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g runtime +
        slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g runtime := by
  rw [← PqxdhDeploymentIdealLaterCompile.ideal_compile_server setup codec route checks phase1 phase2 ensureInit bounds
    mode first second budget respects event claim g runtime]
  exact chain_slot_later_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode first
    second budget respects post postRespects event claim g runtime

/-- The later `ideal_world` (design-v2 section 10, U-L2 composed with U-L3): under `Phase1ReadBack` and `Phase2ReadBack`, for a run-phase budget-respecting `first` and every post adversary, item 2's logged two-slot world of the compiled LQ-F program at `g`'s decision and the later record world with the ideal environment of the target of `g` and the environment's reveal give the per-target decision the same probability (`PqxdhDeploymentIdealLaterCompile.ideal_compile_server`, `PqxdhDeploymentIdealLaterEnv.c6_idealGame_decide`). -/
theorem ideal_world_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhDeploymentLaterServerItemTargets.laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        2] {true} =
      𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftLater.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second] {true} :=
  (PqxdhDeploymentIdealLaterCompile.ideal_compile_server setup codec route checks phase1 phase2 ensureInit bounds mode
    first second budget respects event claim g runtime).trans
    (PqxdhDeploymentIdealLaterEnv.c6_idealGame_decide setup codec route checks budget g ensureInit runtime bounds mode
      first second event claim)

/-- The later `ideal_world` on the record lift's view (the later form of `PqxdhDeploymentIdealHandoff.ideal_world_view`): item 2's logged two-slot world of the compiled LQ-F program at `g`'s decision and `dec_g` on the view of the all-real later chain world with the ideal environment of the target of `g` and the environment's reveal have the same probability (`ideal_world_later`, `PqxdhRecordLiftLaterWorlds.laterReal_game`). -/
theorem ideal_world_view_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhDeploymentLaterServerItemTargets.laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        2] {true} =
      𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true} := by
  rw [ideal_world_later setup codec checks route ensureInit phase1 phase2 bounds mode first second budget respects
    event claim g runtime, Functor.map_map]
  have viewed := congrArg (fun computation => (fun observed => observed.any (decisionOn setup codec budget event claim g))
    <$> computation) (PqxdhRecordLiftLaterWorlds.laterReal_game setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId
      bounds mode envReveal first second)
  simp only [PqxdhRecordLiftLater.game, Functor.map_map] at viewed
  rw [← viewed]
  simp only [PqxdhDeploymentIdealHandoff.viewObserved_chainView]

/-- C1-C5, one-sided: the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability of `dec_g` on the view of the all-real later chain world with the ideal environment of the target of `g` and the environment's reveal, plus `kemLossL` and `slotLossL`. -/
theorem chain_view_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true} +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g
        runtime) := by
  rw [← ideal_world_view_later (Reader := Reader) setup codec checks route ensureInit phase1 phase2 bounds mode first
    second budget respects event claim g runtime]
  exact chain_slot_later setup functional codec checks route ensureInit phase1 phase2 correct bounds mode first second
    budget respects post postRespects event claim g runtime

/-- C1-C5, two-sided: the probability that the LQ-F game ends with the event and the claim designating `g` and the probability of `dec_g` on the view of the all-real later chain world with the ideal environment of the target of `g` differ by at most `kemLossL + slotLossL`. -/
theorem chain_close_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      (𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true}).toReal| ≤
      kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g runtime +
        slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g runtime := by
  rw [← ideal_world_view_later (Reader := Reader) setup codec checks route ensureInit phase1 phase2 bounds mode first
    second budget respects event claim g runtime]
  exact chain_slot_later_close setup functional codec checks route ensureInit phase1 phase2 correct bounds mode first
    second budget respects post postRespects event claim g runtime

end Chain

/-! ### C6: the slot conjunction on the later view -/

section Slots
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out R : Type}

/-- The Server-side form of `PqxdhDeploymentIdealLaterSlots.later_slots`: under `Phase1ReadBack`, on every outcome of the all-real later chain world with the ideal environment of a target, for every reveal and post adversary, the view's handle-to-slot map satisfies the three Server-side conjuncts of `IdealSlots` (`ServerSlots`) for the run-phase transcript. The later world is the run-phase world followed by the E-only continuation (`PqxdhRecordLiftLaterWorlds.laterChains_split`), which keeps the control and the ledger (`PqxdhDeploymentIdealLaterSlots.continueWith_noinstall`), so `PqxdhDeploymentHeadlineChain.real_slots_server` carries over. -/
theorem later_real_slots_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    {count : ℕ} (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode)
    (reveal : PqxdhDeploymentEnvironment.EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count ×
      PqxdhDeploymentIdealSteps.SplitBk) → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out) :
    ∀ result ∈ support (laterRealChains setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode reveal first second),
      ∀ value, (chainView result).result = some value →
        ServerSlots setup.source.crypto codec setup.serverKeyId t (chainView result).slots value.2.1.transcript := by
  intro result member value found
  rw [laterRealChains, PqxdhRecordLiftLaterWorlds.laterChains_split, mem_support_bind_iff] at member
  obtain ⟨run, runMember, later⟩ := member
  obtain ⟨controlSame, kept⟩ := PqxdhDeploymentIdealLaterSlots.continueWith_noinstall setup codec checks _ route t
    ensureInit identityIndex runtime reveal second run result later
  rcases runOutcome : run.1.1 with _ | runValue
  · rw [runOutcome] at kept
    have none : result.1.1 = none := Option.map_eq_none_iff.mp kept
    simp [chainView, PqxdhRecordLiftIdeal.viewOf, none] at found
  · rw [runOutcome] at kept
    obtain ⟨laterValue, laterFound, laterSame⟩ := Option.map_eq_some_iff.mp kept
    have runFound : (chainView run).result = some (runValue.2.1.1, runValue.2.1.2, runValue.2.2) := by
      simp [chainView, PqxdhRecordLiftIdeal.viewOf, runOutcome]
    have slots := PqxdhDeploymentHeadlineChain.real_slots_server setup codec checks route phase1 t ensureInit
      identityIndex runtime bounds mode first run runMember _ runFound
    have valueSame : value = (laterValue.2.1.1, laterValue.2.1.2, laterValue.2.2) := by
      simp only [chainView, PqxdhRecordLiftIdeal.viewOf, laterFound, Option.map_some, Option.some.injEq] at found
      exact found.symm
    have ledgerSame : value.2.1 = runValue.2.1.2 := by
      rw [valueSame]
      exact congrArg (fun pair => pair.2) laterSame
    have slotsSame : (chainView result).slots = (chainView run).slots := by
      simp only [chainView, PqxdhRecordLiftIdeal.viewOf, controlSame]
    rw [ledgerSame, slotsSame]
    exact slots

open Classical in
/-- An event on the later view without `IdealSlots` (the later form of `PqxdhDeploymentHeadlineChain.view_unslotted`): under `Phase1ReadBack` and `Phase2ReadBack`, the probability that an event of the view of the all-real later chain world holds while `IdealSlots` of the target fails is at most the probability of the Beacon-side anomaly on the run-phase record world of `first` (`PqxdhDeploymentIdealLaterSlots.later_slots`, `later_anomaly_eq`). -/
theorem later_view_unslotted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) {count : ℕ} (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (reveal : PqxdhDeploymentEnvironment.EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count ×
      PqxdhDeploymentIdealSteps.SplitBk) → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (event : View 2 (PqxdhDeploymentEnvironment.EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count ×
      PqxdhDeploymentIdealSteps.SplitBk)) Out → Bool) :
    𝒟[(fun view => decide (event view = true ∧ ¬∀ value, view.result = some value →
          IdealSlots setup.source.crypto codec setup.serverKeyId t view.slots value.2.1.transcript)) <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode reveal first second)] {true} ≤
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode first] {true} := by
  rw [← PqxdhDeploymentIdealLaterSlots.later_anomaly_eq setup codec route checks t ensureInit identityIndex runtime
    setup.serverKeyId bounds mode reveal first second]
  rw [UniformTargetSelection.chance_eq_vcvioLegacy, UniformTargetSelection.chance_eq_vcvioLegacy]
  refine probEvent_mono fun view member held => ?_
  rw [support_map] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  obtain ⟨value, unslotted⟩ := Classical.not_forall.mp held.2
  obtain ⟨found, failed⟩ := Classical.not_imp.mp unslotted
  exact ⟨value, found, (PqxdhDeploymentIdealLaterSlots.later_slots setup codec route checks phase1 phase2 t ensureInit
    identityIndex runtime bounds mode reveal first second result resultMember value found).resolve_left failed⟩

end Slots

section SlotsChain
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

open Classical in
/-- C1-C6 for Server-side claims: under the chain's premises, the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability of `dec_g ∧ ISs_g` (`serverSlotted`) on the view of the all-real later chain world with the ideal environment of the target of `g`, plus `kemLossL` and `slotLossL`; no anomaly term. -/
theorem chain_server_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[serverSlotted setup codec budget event claim g <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true} +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g
        runtime) := by
  refine (chain_view_later (Reader := Reader) setup functional codec checks route ensureInit phase1 phase2 correct
    bounds mode first second budget respects post postRespects event claim g runtime).trans_eq ?_
  congr 3
  rw [Functor.map_map, Functor.map_map]
  congr 1
  refine PqxdhDeploymentKemTransfer.map_support_congr _ _ _ fun result member => ?_
  simp only [serverSlotted]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨fun held => ⟨held, later_real_slots_server setup codec checks route phase1 (Target.ofCE budget g) ensureInit 0
    runtime bounds mode envReveal first second result member⟩, And.left⟩

open Classical in
/-- C1-C6 with `IdealSlots` (Beacon-capable claims): the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability of `dec_g ∧ IS_g` (`slotted`) on the view of the all-real later chain world with the ideal environment of the target of `g`, plus the probability of the Beacon-side anomaly on the run-phase record world of `first` (`PqxdhDeploymentIdealLaterSlots.later_view_slots_le`), plus `kemLossL` and `slotLossL`. -/
theorem chain_slots_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[slotted setup codec budget event claim g <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true} +
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode first] {true} +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g
        runtime) :=
  (chain_view_later (Reader := Reader) setup functional codec checks route ensureInit phase1 phase2 correct bounds mode
    first second budget respects post postRespects event claim g runtime).trans (add_le_add (add_le_add
      (PqxdhDeploymentIdealLaterSlots.later_view_slots_le setup codec route checks phase1 phase2 (Target.ofCE budget g)
        ensureInit 0 runtime bounds mode envReveal first second
        (fun view => (viewObserved view).any (decisionOn setup codec budget event claim g))) le_rfl) le_rfl)

open Classical in
/-- C1-C6 with the anomaly term bounded (Beacon-capable claims, one-sided): the probability that the LQ-F game ends with the event and the claim designating `g` is at most the probability of `dec_g ∧ IS_g` on the view of the all-real later chain world with the ideal environment of the target of `g`, plus `β_g` of the run-phase adversary `first` (`PqxdhDeploymentHeadlineAnomaly.beta`, through `anomaly_beta`: `anomaly_le_pk` on `first`'s run, then `ptc_bound`), plus `kemLossL` and `slotLossL`. -/
theorem chain_beta_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[slotted setup codec budget event claim g <$>
        (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true} +
      PqxdhDeploymentHeadlineAnomaly.beta setup codec route checks ensureInit bounds mode first budget g runtime +
      ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL setup codec checks route ensureInit bounds mode first second budget post event claim g
        runtime) :=
  (chain_slots_later (Reader := Reader) setup functional codec checks route ensureInit phase1 phase2 correct bounds
    mode first second budget respects post postRespects event claim g runtime).trans (add_le_add (add_le_add
      (add_le_add le_rfl (PqxdhDeploymentHeadlineAnomaly.anomaly_beta setup functional codec checks route ensureInit
        phase1 phase2 bounds mode first budget g runtime)) le_rfl) le_rfl)

end SlotsChain

/-! ### C7: the later record lift at the ideal environment of a target -/

section Lift
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- C7 (later form): for every view event, the probabilities on the record lift's views of the all-real later chain world and of the later record-ideal world `laterIdealRecords`, both with the ideal environment of the target of `g`, the environment's reveal and the post adversary, differ by at most `recLossL`. The frame is `PqxdhDeploymentIdealFrame.frame_idealD` (premises `KemBound setup caps` and the total query bound `qInit` of the runtime initializer); the lift is `PqxdhRecordLiftLaterLift.later_record_lift` (contract `SourceFullCorrect`; the post adversary within its post budget). -/
theorem records_close_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) Out → Bool) :
    ENNReal.ofReal |(𝒟[event <$> (chainView <$> laterRealChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true}).toReal -
        (𝒟[event <$> (ctxView <$> laterIdealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second)] {true}).toReal| ≤
      recLossL setup codec checks route ensureInit bounds mode first second budget post g runtime fallback caps qInit
        event := by
  have lift := (PqxdhRecordLiftLaterLift.later_record_lift setup codec route setup.serverKeyId bounds 2 setup.hmac
    fallback).2 correct (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode envReveal first second budget post respects postRespects event
  rw [Functor.map_map, Functor.map_map]
  exact lift.1

/-- C7 (later form), one-sided: a view event on the all-real later chain world has at most its probability on `laterIdealRecords` plus `recLossL`. -/
theorem records_le_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (event : View 2 (EnvG KemSK budget) Out → Bool) :
    𝒟[event <$> (chainView <$> laterRealChains setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode envReveal first second)] {true} ≤
      𝒟[event <$> (ctxView <$> laterIdealRecords setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode envReveal first second)] {true} +
      recLossL setup codec checks route ensureInit bounds mode first second budget post g runtime fallback caps qInit
        event :=
  PqxdhDeploymentHeadlineChain.le_add_of_ofReal_abs (chance_ne_top _ _) (chance_ne_top _ _)
    (records_close_later setup codec checks route correct caps bounded ensureInit qInit initBound bounds mode first
      second budget respects post postRespects g runtime fallback event)

end Lift

/-! ### The exact split over the tight target domain -/

section Split
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- The exact split for an event that names a designated claim (LQ-F form): if the event implies that the claim's handle has a budgeted designation, then for a run-phase budget-respecting `first` and every post adversary the probability that the LQ-F game ends with the event is the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of the probability that it ends with the event and the claim designating `g` (`PqxdhDeploymentLaterTargetRange.split_create_later`). -/
theorem split_named_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (runtime : A)
    (named : ∀ observed, event observed = true →
      (PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim observed).isSome) :
    𝒟[(fun outcome => happens event outcome) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
      ∑ g : Fin budget.accept × Fin budget.create,
        𝒟[(fun outcome => decide (happens event outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim outcome =
            some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  rw [← PqxdhDeploymentLaterTargetRange.split_create_later setup codec checks route ensureInit phase1 phase2 bounds mode
    first second budget respects event claim runtime]
  congr 3
  funext outcome
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  refine ⟨fun held => ⟨held, ?_⟩, And.left⟩
  unfold happens at held
  unfold PqxdhDeploymentLaterTargetRange.eligibleL
  cases found : PqxdhDeploymentLaterServerTransfer.observeGame outcome.1 with
  | none => simp [found] at held
  | some observed =>
      rw [found, Option.any_some] at held
      have targeted := named observed held
      simp only [Option.bind_some]
      unfold PqxdhDeploymentKemTransfer.target at targeted
      cases named : claim observed with
      | none => simp [named] at targeted
      | some handle =>
          rw [named, Option.bind_some] at targeted
          simp only [Option.bind_some]
          unfold PqxdhDeploymentTranscript.designateIn at targeted
          cases chosen : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
              observed.2.1.transcript handle with
          | none => simp [chosen] at targeted
          | some _ => rfl

end Split

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_slot_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_slot_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_slot_later_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_slot_later_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_ideal_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_ideal_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_ideal_later_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_ideal_later_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.ideal_world_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.ideal_world_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.ideal_world_view_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.ideal_world_view_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_view_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_view_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_close_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_close_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.later_real_slots_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.later_real_slots_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.later_view_unslotted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.later_view_unslotted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_server_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_slots_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_slots_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_beta_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.chain_beta_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.records_close_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.records_close_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.records_le_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.records_le_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.split_named_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineChain.split_named_later
