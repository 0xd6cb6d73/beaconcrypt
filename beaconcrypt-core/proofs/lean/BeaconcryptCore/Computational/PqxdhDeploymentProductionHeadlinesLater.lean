-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor

/-!
# Production composition of items 3 and 7: the later-quantum CE-12 headlines (P3 and P4 step 1) on the production source game

Every theorem of this module is the production form of a published later-quantum CE-12 headline of item 3 (sections "CE-12 P3 ..." and "CE-12 P4: step 1 ..." of `doc/impl/common-deployment-experiment.md`) and keeps the frozen theorem's name: the frozen statement instantiated at the production codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and route `route′ = RawCtxFrameDecoding.sender reader.model` of item 7, with every probability of the LQ-F experiment `PqxdhDeploymentLaterServerGame.game … 0 … first second` replaced by the probability of the same event, read back through `PqxdhBoundaryDeploymentLater.unwrap`, on the LQ-F production source game `PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 … first second` of PB-D (`PqxdhDeploymentProductionTransfer.chance_later`, from `later_evalDist` at index 0). The bound is the frozen one, word for word at codec′ and route′; the classical run-phase terms of the symbolic forms (`ctGapTerm`, `a1Term`, `a2pubTerm`, ... of `first`) stay CE-model terms at codec′ and route′ (`PqxdhDeploymentProductionHeadlinesClassical.ctGapTerm_source` reads the explicit one on the classical source game). Premises as in the classical module: the frozen ones at codec′ and route′, `Phase1ReadBack` and `Phase2ReadBack` stated at `codec`. The later mode stays confidentiality only: there is no later origin, UKS, binding or authentication form, because CE-12 has none. No assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater

variable {ι KemSK Reader Response Message Root A X Out : Type} {baseSpec : OracleSpec ι}

section
open PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later` (frozen: **CE-KT-L, one-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event
        claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) checks budget g ensureInit bounds mode first
          second).run runtime] {true} +
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget
        post event claim g runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode first second budget
      respects post postRespects event claim g runtime

end

section
open PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_close` (frozen: **CE-KT-L, two-sided** (design.md section 9.1, `|Pr_LQF[D_g] − Pr_{IL_g}[D_g]| ≤ kemLossL g d_g + slotLossL g d_g`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true}).toReal -
      (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event
        claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) checks budget g ensureInit bounds mode first
          second).run runtime] {true}).toReal| ≤
      kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim g runtime +
        slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget post event
          claim g runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_close setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode first second budget
      respects post postRespects event claim g runtime

end

section
open PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le` (frozen: **CE-KT-L, summed, one-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_sum_le (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (runtime : A) :
    𝒟[((fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId claim
          outcome).isSome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime)) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode first second budget
      respects post postRespects event claim runtime

end

section
open PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum` (frozen: **CE-KT-L, summed, two-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId claim
          outcome).isSome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc)
            runtime +
          slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget post event
            claim (g.1, g.2.castSucc) runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode first second budget
      respects post postRespects event claim runtime

end

section
open PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world` (frozen: **CE-KT-L, World form, one-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_world (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event claim g)) <$>
        PqxdhRecordLiftLater.run setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model)
          (PqxdhDeploymentIdealEnv.envGD setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second] {true} +
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim g
        runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget
        post event claim g runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode first second budget
      respects post postRespects event claim g runtime

end

section
open PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_close` (frozen: **CE-KT-L, World form, two-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_world_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true}).toReal -
      (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event claim g)) <$>
        PqxdhRecordLiftLater.run setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model)
          (PqxdhDeploymentIdealEnv.envGD setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode envReveal first second] {true}).toReal| ≤
      kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim g runtime +
        slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget post event
          claim g runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_close setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode first second budget
      respects post postRespects event claim g runtime

end

section
open PqxdhDeploymentLaterHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_sum` (frozen: **CE-KT-L, World form, summed, two-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_world_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId claim
          outcome).isSome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any
            (decisionOn setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event claim
              (g.1, g.2.castSucc))) <$>
          PqxdhRecordLiftLater.run setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model)
            (PqxdhDeploymentIdealEnv.envGD setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit 0
              runtime) setup.serverKeyId bounds mode envReveal first second] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc)
            runtime +
          slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget post event
            claim (g.1, g.2.castSucc) runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_world_sum setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode first second budget
      respects post postRespects event claim runtime

end

section
open PqxdhDeploymentLaterHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineApp.ce_app_later_target` (frozen: **CE-APP-L, per target**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget appClaim) outcome =
        true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (appHandle appClaim) outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime]
        {true} ≤
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
        (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
        (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds .P first budget g runtime +
      recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback caps
          qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineApp.ce_app_later_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim g

end

section
open PqxdhDeploymentLaterHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineApp.ce_app_later` (frozen: **CE-APP-L** (design.md section 9.1)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[((fun outcome => happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget appClaim) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime]
        {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineApp.ce_app_later setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim

end

section
open PqxdhDeploymentLaterHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineApp.ce_app_server_later_target` (frozen: **CE-APP-L on a Server peer, per target**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_server_later_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (appPeerEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget appClaim)
        outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (appHandle appClaim) outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime]
        {true} ≤
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
        (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
        (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback caps
          qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineApp.ce_app_server_later_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim g

end

section
open PqxdhDeploymentLaterHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineApp.ce_app_server_later` (frozen: **CE-APP-L on a Server peer**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_server_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[((fun outcome => happens (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget appClaim) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime]
        {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineApp.ce_app_server_later setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim

end

section
open PqxdhDeploymentLaterHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

open Classical in
/-- Production form of `PqxdhDeploymentLaterHeadlineLor.ce_lor_later_target` (frozen: **CE-LOR-L, per target**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_later_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[((fun outcome => decide (happens (lorWinEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => decide (happens (lorEligEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal| ≤
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
        (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
        (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) lorClaim g runtime) +
      recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback caps
          qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            guess filter)
          lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
          post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback
            caps qInit
          (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
            (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget filter)
            lorClaim g)) +
      2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
        checks ensureInit bounds .P first budget g runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineLor.ce_lor_later_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback guess filter g

end

section
open PqxdhDeploymentLaterHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

open Classical in
/-- Production form of `PqxdhDeploymentLaterHeadlineLor.ce_lor_later` (frozen: **CE-LOR-L** (design.md section 9.1)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[((fun outcome => happens (lorWinEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
          filter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => happens (lorEligEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget filter)
          outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget filter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineLor.ce_lor_later setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback guess filter

end

section
open PqxdhDeploymentLaterHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

open Classical in
/-- Production form of `PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later_target` (frozen: **CE-LOR-L on Server peers, per target**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_server_later_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[((fun outcome => decide (happens (lorWinPeerEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget guess filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => decide (happens (lorEligPeerEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal| ≤
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
        (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
        (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget guess filter) lorClaim g runtime) +
      recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback caps
          qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget guess filter) lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
          (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
          post (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
            setup.serverKeyId budget filter) lorClaim g runtime) +
        recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback
            caps qInit
          (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
            (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget filter) lorClaim g)) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback guess filter g

end

section
open PqxdhDeploymentLaterHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

open Classical in
/-- Production form of `PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later` (frozen: **CE-LOR-L on Server peers**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_server_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[((fun outcome => happens (lorWinPeerEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
          filter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => happens (lorEligPeerEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          filter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                  setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc)))) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback guess filter

end

section
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym` (frozen: **CE-APP-L, symbolic eligibility** (any claimed handle, mode P)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds first second budget respects post postRespects
      runtime fallback appClaim identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolic.ce_app_server_later_sym` (frozen: **CE-APP-L on a Server peer, symbolic eligibility** (mode P)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_server_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => appPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolic.ce_app_server_later_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects bounds first second budget respects post postRespects runtime fallback appClaim identityFallback
      ordinaryFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym` (frozen: **CE-APP-L on a Beacon owner, symbolic eligibility** (mode P)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => appOwnerSym setup appClaim (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds first second budget respects post postRespects runtime fallback
      appClaim a1Fallback signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym` (frozen: **CE-KT-L, symbolic eligibility** (any claimed handle)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => ktSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) event claim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds mode first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded shortRejects
      frameReadBack writable law spread adapter bounds mode first second budget respects post postRespects event claim
      runtime identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_server_later_sym` (frozen: **CE-KT-L, Server-side symbolic eligibility**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_server_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => ktPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) event claim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first budget runtime identityFallback
        ordinaryFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_server_later_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct shortRejects bounds mode first
      second budget respects post postRespects event claim runtime identityFallback ordinaryFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym` (frozen: **CE-KT-L, Beacon-side symbolic eligibility**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_beacon_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => ktOwnerSym setup event claim (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded frameReadBack
      writable law spread adapter bounds mode first second budget respects post postRespects event claim runtime
      a1Fallback signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later` (frozen: `symbolic_lor` on the LQ-F game (mode P; the later forms of VC rows SSX-b2s, SS-b2s and 173 on symbolic eligibility)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal) -
      ((𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            guess nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound` (frozen: `symbolic_lor_later` with CE-LOR-L's bound (`PqxdhDeploymentLaterHeadlineLor.ce_lor_later` at the NoBundleFailure filter)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later` (frozen: `symbolic_lor_server` on the LQ-F game (mode P; the later forms of VC rows SSX-s2b, SS-s2b on Server-side symbolic eligibility)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_server_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal) -
      ((𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget guess nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks shortRejects (RawCtxFrameDecoding.sender reader.model)
      ensureInit ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) bounds first second budget respects
      runtime guess identityFallback ordinaryFallback

end

section
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later_bound` (frozen: `symbolic_lor_server_later` with CE-LOR-L's Server-side bound (`PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later` at the NoBundleFailure filter, no `β_g`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_server_later_bound (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                  setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))))) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later_bound setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds first second budget
      respects post postRespects runtime fallback guess identityFallback ordinaryFallback

end

section
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentLaterHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineGated.ce_app_later_target_billed` (frozen: `ce_app_later_target` (`PqxdhDeploymentLaterHeadlineApp.ce_app_later_target`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (g : Fin budget.accept × Fin budget.capacity) :
    (𝒟[((fun outcome => decide (happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget appClaim) outcome =
        true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (appHandle appClaim) outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime]
        {true} ≤
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
        (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
        (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds .P first budget g runtime +
      recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback caps
          qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineGated.ce_app_later_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim g

end

section
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentLaterHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineGated.ce_app_later_billed` (frozen: `ce_app_later` (`PqxdhDeploymentLaterHeadlineApp.ce_app_later`, CE-APP-L) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    (𝒟[((fun outcome => happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget appClaim) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime]
        {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineGated.ce_app_later_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim

end

section
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentLaterHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

open Classical in
/-- Production form of `PqxdhDeploymentLaterHeadlineGated.ce_lor_later_target_billed` (frozen: `ce_lor_later_target` (`PqxdhDeploymentLaterHeadlineLor.ce_lor_later_target`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_later_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) (g : Fin budget.accept × Fin budget.capacity) :
    (ENNReal.ofReal |(𝒟[((fun outcome => decide (happens (lorWinEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => decide (happens (lorEligEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal| ≤
      ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
        (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
        (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) lorClaim g runtime) +
      recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback caps
          qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            guess filter)
          lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
          post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post g runtime fallback
            caps qInit
          (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
            (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget filter)
            lorClaim g)) +
      2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
        checks ensureInit bounds .P first budget g runtime) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineGated.ce_lor_later_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback guess filter g

end

section
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentLaterHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

open Classical in
/-- Production form of `PqxdhDeploymentLaterHeadlineGated.ce_lor_later_billed` (frozen: `ce_lor_later` (`PqxdhDeploymentLaterHeadlineLor.ce_lor_later`, CE-LOR-L) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_later_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    (ENNReal.ofReal |(𝒟[((fun outcome => happens (lorWinEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
          filter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => happens (lorEligEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget filter)
          outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget filter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineGated.ce_lor_later_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback guess filter

end

section
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineGated.ce_app_later_sym_billed` (frozen: `ce_app_later_sym` (`PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineGated.ce_app_later_sym_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds first second budget respects post postRespects
      runtime fallback appClaim identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineGated.ce_app_beacon_later_sym_billed` (frozen: `ce_app_beacon_later_sym` (`PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_later_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => appOwnerSym setup appClaim (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineGated.ce_app_beacon_later_sym_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds first second budget respects post postRespects runtime fallback
      appClaim a1Fallback signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed` (frozen: `symbolic_lor_later_bound` (`PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentLaterHeadlineClosed
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed` (frozen: `symbolic_lor_later` closed (`PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le` at the run-phase adversary `first`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_closed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal) -
      ((𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            guess nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentLaterHeadlineClosed
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed` (frozen: `symbolic_lor_later_bound` closed (`PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le` at the run-phase adversary `first`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_closed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentLaterHeadlineClosed
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- Production form of `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed` (frozen: `symbolic_lor_later_bound` closed and billed (`PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed` with `ctCollTerm` replaced by `ε_ctcoll`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_closed_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentLaterHeadlineGated.LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P
        first second budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

end BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_sum_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_world_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_world_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_world_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_world_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_server_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_server_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_server_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_server_later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_server_later_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_server_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_server_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_server_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_beacon_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_beacon_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_server_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_server_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_beacon_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_kt_beacon_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_server_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_server_later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_server_later_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_lor_later_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_later_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_beacon_later_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.ce_app_beacon_later_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater.symbolic_lor_later_bound_closed_billed
