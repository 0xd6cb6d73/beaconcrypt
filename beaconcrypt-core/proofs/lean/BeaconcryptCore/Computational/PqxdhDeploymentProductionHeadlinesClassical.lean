-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks

/-!
# Production composition of items 3 and 7: the classical CE-12 headlines (P1 and P2) on the production source game

Every theorem of this module is the production form of a published CE-12 headline of item 3 (sections "CE-12 ..." and "CE-12 P2 ..." of `doc/impl/common-deployment-experiment.md`) and keeps the frozen theorem's name: the frozen statement instantiated at the production codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and route `route′ = RawCtxFrameDecoding.sender reader.model` of item 7, with every probability of the CE experiment `PqxdhDeploymentSecrecy.game … 0 …` replaced by the probability of the same event, read back through `PqxdhBoundaryDeployment.unwrap`, on the classical production source game `PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 …` of PB-D (`PqxdhDeploymentProductionTransfer.chance`, from `classical_evalDist` at index 0). The bound is the frozen one, word for word at codec′ and route′: its losses, ideal games, record worlds, explicit terms and advantages are CE-model quantities at the production instance. Premises: the frozen ones at codec′ and route′, except that `Phase1ReadBack` and `Phase2ReadBack` are stated at `codec` and transported by `PqxdhBoundaryDeploymentStep.phase1_withReader` and `phase2_withReader` (`Iff.rfl`); `FrameReadBack` and `ReadWritable` are carried at codec′ exactly where the frozen theorem takes them (their reading at codec′: `PqxdhDeploymentProductionTransfer.frameReadBack_withReader`, `readWritable_withReader`). No selected headline takes `DecoderAgreement`. `ctGapTerm` stays explicit (F-ct2); `ctGapTerm_source` and `ctCollTerm_source` state that the two explicit experiment terms at codec′ and route′ are the probabilities of their events on the classical source game. Each proof is `simp only` with the transfer lemma followed by the frozen theorem. No assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical

variable {ι KemSK Reader Response Message Root A X Out : Type} {baseSpec : OracleSpec ι}

section
open PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

/-- Production form of `PqxdhDeploymentHeadlineKeyTransfer.ce_kt` (frozen: **CE-KT, one-sided** (design-v2 section 4.1, the probe `kt_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) checks budget g ensureInit bounds mode adversary).run
          runtime] {true} +
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineKeyTransfer.ce_kt setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode adversary budget
      respects event claim g runtime

end

section
open PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

/-- Production form of `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_close` (frozen: **CE-KT, two-sided** (design-v2 section 4.1)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal -
      (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) checks budget g ensureInit bounds mode adversary).run
          runtime] {true}).toReal| ≤
      kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime +
        slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineKeyTransfer.ce_kt_close setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode adversary budget
      respects event claim g runtime

end

section
open PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

/-- Production form of `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum_le` (frozen: **CE-KT, summed, one-sided** (design-v2 section 4.1)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_sum_le (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    𝒟[((fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId claim outcome).isSome)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime)) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum_le setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode adversary budget
      respects event claim runtime

end

section
open PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

/-- Production form of `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum` (frozen: **CE-KT, summed, two-sided** (design-v2 section 4.1, `ce_kt_sum`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId claim outcome).isSome)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
            (g.1, g.2.castSucc)
            runtime +
          slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
              (g.1, g.2.castSucc)
            runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode adversary budget
      respects event claim runtime

end

section
open PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

/-- Production form of `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world` (frozen: **CE-KT, World form, one-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_world (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event claim g)) <$>
        PqxdhRecordLiftWorld.run setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model)
          (PqxdhDeploymentIdealEnv.envGD setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} +
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode adversary budget
      respects event claim g runtime

end

section
open PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

/-- Production form of `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_close` (frozen: **CE-KT, World form, two-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_world_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          claim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal -
      (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event claim g)) <$>
        PqxdhRecordLiftWorld.run setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model)
          (PqxdhDeploymentIdealEnv.envGD setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true}).toReal| ≤
      kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime +
        slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim g runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_close setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode adversary budget
      respects event claim g runtime

end

section
open PqxdhDeploymentHeadlineKeyTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss)

/-- Production form of `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_sum` (frozen: **CE-KT, World form, summed, two-sided**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_world_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    |(𝒟[((fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId claim outcome).isSome)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any
            (decisionOn setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget event claim
              (g.1, g.2.castSucc))) <$>
          PqxdhRecordLiftWorld.run setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model)
            (PqxdhDeploymentIdealEnv.envGD setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (Target.ofCE budget (g.1, g.2.castSucc)) ensureInit 0
              runtime) setup.serverKeyId bounds mode adversary] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
            (g.1, g.2.castSucc)
            runtime +
          slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
              (g.1, g.2.castSucc)
            runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineKeyTransfer.ce_kt_world_sum setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds mode adversary budget
      respects event claim runtime

end

section
open PqxdhDeploymentHeadlineOrigin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth publicationTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (Direction originEvent orClaim)

/-- Production form of `PqxdhDeploymentHeadlineOrigin.ce_or_b2s_target` (frozen: **CE-OR b2s, per target** (design-v2 section 4.2)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (originEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .b2s)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s)
        (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s)
        (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s) g runtime) +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s)
          (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s) g) +
      publicationTerm budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineOrigin.ce_or_b2s_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlineOrigin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth publicationTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (Direction originEvent orClaim)

/-- Production form of `PqxdhDeploymentHeadlineOrigin.ce_or_b2s` (frozen: **CE-OR b2s** (design-v2 section 4.2, `ce_or_b2s`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[((fun outcome => happens (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .b2s) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .b2s)
              (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineOrigin.ce_or_b2s setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlineOrigin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth publicationTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (Direction originEvent orClaim)

/-- Production form of `PqxdhDeploymentHeadlineOrigin.ce_or_s2b_target` (frozen: **CE-OR s2b, per target** (design-v2 section 4.2)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (originEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .s2b)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds mode adversary budget g runtime +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b)
          (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) g) +
      publicationTerm budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineOrigin.ce_or_s2b_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlineOrigin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth publicationTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (Direction originEvent orClaim)

/-- Production form of `PqxdhDeploymentHeadlineOrigin.ce_or_s2b` (frozen: **CE-OR s2b** (design-v2 section 4.2, `ce_or_s2b`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[((fun outcome => happens (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineOrigin.ce_or_s2b setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlineUks
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth bindingTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (uksReceiverEvent uksReceiverClaim uksSenderEvent uksSenderClaim)

/-- Production form of `PqxdhDeploymentHeadlineUks.ce_uks_b2s_target` (frozen: **CE-UKS, receiver side, per target** (design-v2 section 4.3)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (uksReceiverEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model))
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (uksReceiverClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (uksReceiverEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (uksReceiverClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (uksReceiverEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (uksReceiverClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (uksReceiverEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model))
          (uksReceiverClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) g) +
      bindingTerm (inputG caps qInit budget bounds) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineUks.ce_uks_b2s_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlineUks
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth bindingTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (uksReceiverEvent uksReceiverClaim uksSenderEvent uksSenderClaim)

/-- Production form of `PqxdhDeploymentHeadlineUks.ce_uks_b2s` (frozen: **CE-UKS, receiver side** (design-v2 section 4.3, the CE form of b2s-UKSr)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[((fun outcome => happens (uksReceiverEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (uksReceiverEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (uksReceiverClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (uksReceiverEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (uksReceiverClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (uksReceiverEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model))
              (uksReceiverClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc)) +
          bindingTerm (inputG caps qInit budget bounds)) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineUks.ce_uks_b2s setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlineUks
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth bindingTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (uksReceiverEvent uksReceiverClaim uksSenderEvent uksSenderClaim)

/-- Production form of `PqxdhDeploymentHeadlineUks.ce_uks_sender_target` (frozen: **CE-UKS, sender side, per target** (design-v2 section 4.3)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sender_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (uksSenderEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model))
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds mode adversary budget g runtime +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model))
          (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) g) +
      bindingTerm (inputG caps qInit budget bounds) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineUks.ce_uks_sender_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlineUks
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth bindingTerm)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (uksReceiverEvent uksReceiverClaim uksSenderEvent uksSenderClaim)

/-- Production form of `PqxdhDeploymentHeadlineUks.ce_uks_sender` (frozen: **CE-UKS, sender side** (design-v2 section 4.3, `ce_uks_sender`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sender (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[((fun outcome => happens (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model))
              (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc)) +
          bindingTerm (inputG caps qInit budget bounds)) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineUks.ce_uks_sender setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)

/-- Production form of `PqxdhDeploymentHeadlineApp.ce_app_target` (frozen: **CE-APP, per target** (design-v2 section 4.4)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget appClaim) outcome =
        true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (appHandle appClaim) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds .P adversary budget g runtime +
      recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineApp.ce_app_target setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim g

end

section
open PqxdhDeploymentHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)

/-- Production form of `PqxdhDeploymentHeadlineApp.ce_app` (frozen: **CE-APP** (design-v2 section 4.4, `ce_app`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[((fun outcome => happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget appClaim) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineApp.ce_app setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim

end

section
open PqxdhDeploymentHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)

/-- Production form of `PqxdhDeploymentHeadlineApp.ce_app_server_target` (frozen: **CE-APP on a Server peer, per target** (design-v2 section 4.4, `ce_app_server`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_server_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (appPeerEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget appClaim)
        outcome = true ∧
        designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (appHandle appClaim) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          appClaim) (appHandle appClaim) g runtime) +
      recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineApp.ce_app_server_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim g

end

section
open PqxdhDeploymentHeadlineApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)

/-- Production form of `PqxdhDeploymentHeadlineApp.ce_app_server` (frozen: **CE-APP on a Server peer** (design-v2 section 4.4, `ce_app_server`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[((fun outcome => happens (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget appClaim) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineApp.ce_app_server setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim

end

section
open PqxdhDeploymentHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots peerOf)
open PqxdhDeploymentTranscript (SameView designateIn)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View PublicHiding publicHiding firstTest AdmittedTest testBit)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineLor.ce_lor_target` (frozen: **CE-LOR, per target** (design-v2 section 4.5)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[((fun outcome => decide (happens (lorWinEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => decide (happens (lorEligEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal| ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          guess filter) lorClaim g runtime) +
      recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            guess filter)
          lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget g runtime fallback caps qInit
          (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
            (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget filter)
            lorClaim g)) +
      2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
        checks ensureInit bounds .P adversary budget g runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineLor.ce_lor_target setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback guess filter g

end

section
open PqxdhDeploymentHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots peerOf)
open PqxdhDeploymentTranscript (SameView designateIn)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View PublicHiding publicHiding firstTest AdmittedTest testBit)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineLor.ce_lor` (frozen: **CE-LOR** (design-v2 section 4.5, `ce_lor`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[((fun outcome => happens (lorWinEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
          filter) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => happens (lorEligEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget filter)
          outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc)
                runtime fallback
              caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget filter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc)
              runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineLor.ce_lor setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback guess filter

end

section
open PqxdhDeploymentHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots peerOf)
open PqxdhDeploymentTranscript (SameView designateIn)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View PublicHiding publicHiding firstTest AdmittedTest testBit)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineLor.ce_lor_server_target` (frozen: **CE-LOR on Server peers, per target** (design-v2 section 4.5, `ce_lor_server`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_server_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[((fun outcome => decide (happens (lorWinPeerEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget guess filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => decide (happens (lorEligPeerEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget filter) outcome = true ∧
          designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            lorClaim outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal| ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
        (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget guess filter) lorClaim g runtime) +
      recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget guess filter) lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
          (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
          (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget filter) lorClaim g runtime) +
        recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget g runtime fallback caps qInit
          (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
            (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget filter) lorClaim g)) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineLor.ce_lor_server_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback guess filter g

end

section
open PqxdhDeploymentHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots peerOf)
open PqxdhDeploymentTranscript (SameView designateIn)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View PublicHiding publicHiding firstTest AdmittedTest testBit)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineLor.ce_lor_server` (frozen: **CE-LOR on Server peers** (design-v2 section 4.5, `ce_lor_server`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[((fun outcome => happens (lorWinPeerEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
          filter) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => happens (lorEligPeerEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          filter) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc)
                runtime fallback
              caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                  setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc)))) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineLor.ce_lor_server setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback guess filter

end

section
open PqxdhDeploymentHeadlineGap
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf regOfEntry summarizeReg stepReg accepted acceptedFrom publishedKeys
  keysOfBundle bundleOfReg protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (OwnerForgery OwnerEvent ownerIdentities publishedTuple candidateTuple)

/-- Production form of `PqxdhDeploymentHeadlineGap.server_gap_bound` (frozen: The Server-side gap term). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem server_gap_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(serverGap setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime fallback
          ordinaryFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGap.server_gap_bound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      shortRejects (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) bounds mode adversary budget respects
      runtime fallback ordinaryFallback

end

section
open PqxdhDeploymentHeadlineGap
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf regOfEntry summarizeReg stepReg accepted acceptedFrom publishedKeys
  keysOfBundle bundleOfReg protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (OwnerForgery OwnerEvent ownerIdentities publishedTuple candidateTuple)

/-- Production form of `PqxdhDeploymentHeadlineGap.ce_a1_linked` (frozen: `ce_a1_linked` in the F-ct2 form (design-v2 sections 7.1 and 8)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_a1_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(beaconGap setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget fallback signatureFallback) +
      ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
      (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
      (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget)
      (PqxdhDeploymentServerAuthBills.totalCap caps bounds budget) budget.finish fallback signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGap.ce_a1_linked setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
      bounded (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineGap
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf regOfEntry summarizeReg stepReg accepted acceptedFrom publishedKeys
  keysOfBundle bundleOfReg protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (OwnerForgery OwnerEvent ownerIdentities publishedTuple candidateTuple)

/-- Production form of `PqxdhDeploymentHeadlineGap.sym_gap` (frozen: `sym_gap` in the F-ct2 form (design-v2 sections 7.1 and 8)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem sym_gap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => serverGap setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget outcome || beaconGap
      setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback +
      ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget fallback signatureFallback) +
      ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGap.sym_gap setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
      bounded shortRejects (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime identityFallback ordinaryFallback fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineCollision
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret MlKemCCAOracleSpec OneKeyAdversary
  oneKeyBranchMain oneKeyPrefix oneKeyFinish IsMlKemLogicalDecapsulationQuery)
open PqxdhInitializerSecrecy (runtimeOfImpl kemAmbientImpl)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)

/-- Production form of `PqxdhDeploymentHeadlineCollision.identity_collision_game` (frozen: `identity_collision_game` (design-v2 section 7.4)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem identity_collision_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[((fun outcome => @decide (IdentityCollision setup outcome) (Classical.propDecidable _)) ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      injTerm setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCollision.identity_collision_game setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) bounds mode adversary budget respects
      runtime

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_or_b2s_sym` (frozen: `ce_or_b2s_sym` (design-v2 section 7.3; VC rows L2-origin, b2s-C2, b2s-C2-chosen-fs, b2s-C4, far-b2s-C4 on symbolic eligibility)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_b2s_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(originSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
      .b2s ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .b2s)
              (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_or_b2s_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack shortRejects bounds mode adversary budget respects runtime fallback identityFallback
      ordinaryFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym` (frozen: `ce_or_s2b_sym` (design-v2 section 7.3; VC rows S2b-origin, s2b-C1, s2b-C4, far-s2b-C4 on symbolic eligibility, positions from 2)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(originSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
      .s2b ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_uks_sym` (frozen: `ce_uks_sym` (design-v2 section 7.3; VC row b2s-UKSr on sender symbolic eligibility)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(uksSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model))
              (uksSenderClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc)) +
          bindingTerm (inputG caps qInit budget bounds))) +
      ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_uks_sym setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_app_sym` (frozen: `ce_app_sym` (design-v2 section 7.3; the APP rows on symbolic eligibility of any claimed handle, mode P; the side-specific forms are `ce_app_server_sym` (App-s2b, s2b-S1: `ε_A2pub` only) and `ce_app_beacon_sym` (App-b2s, b2s-S2: `ε_A1 + ctGapTerm` only))). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_sym (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_app_sym setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim
      identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_app_server_sym` (frozen: `ce_app_server_sym` (design-v2 section 7.3; VC rows App-s2b, s2b-S1 on Server-side symbolic eligibility, mode P)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_server_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(appPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appPeerEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
        ordinaryFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_app_server_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects bounds adversary budget respects runtime fallback appClaim identityFallback ordinaryFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym` (frozen: `ce_app_beacon_sym` (design-v2 section 7.3; VC rows App-b2s, b2s-S2 on Beacon-side symbolic eligibility, mode P)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_sym (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(appOwnerSym setup appClaim ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_kt_sym` (frozen: `ce_kt_sym` (design-v2 section 7.3; the KT rows on symbolic eligibility of any claimed handle; for a claim known to be a Server peer, `ce_kt_server_sym` (S3-server) has `ε_A2pub` only, and for a claim known to be an owner, `ce_kt_beacon_sym` (S3-beacon) has `ε_A1 + ctGapTerm` only; A1-root uses the form of its claim's side)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_sym (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (runtime : A) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(ktSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) event claim ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
              reader) setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_kt_sym setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded shortRejects
      frameReadBack writable law spread adapter bounds mode adversary budget respects event claim runtime
      identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_kt_server_sym` (frozen: `ce_kt_server_sym` (design-v2 section 7.3 and section 12's S3-server row; VC row S3-server, and A1-root with a Server-peer claim, on Server-side symbolic eligibility)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_server_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (runtime : A) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(ktPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) event claim ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
              reader) setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_kt_server_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct shortRejects bounds mode
      adversary budget respects event claim runtime identityFallback ordinaryFallback

end

section
open PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- Production form of `PqxdhDeploymentHeadlineSymbolic.ce_kt_beacon_sym` (frozen: `ce_kt_beacon_sym` (design-v2 section 7.3 and section 12's S3-beacon row; VC row S3-beacon, and A1-root with an owner claim, on Beacon-side symbolic eligibility)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_beacon_sym (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (runtime : A) (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(ktOwnerSym setup event claim ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
              reader) setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolic.ce_kt_beacon_sym setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded frameReadBack
      writable law spread adapter bounds mode adversary budget respects event claim runtime a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailure NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (protectedBinding)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt IdentityCollision)
open PqxdhDeploymentHeadlineSymbolic (SymHandle)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest admissibleTest)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

/-- Production form of `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor` (frozen: `symbolic_lor` (design-v2 section 7.5; VC rows SSX-b2s, SS-b2s, 167/173 on symbolic eligibility, with any admitted test handles; the Server-side rows SSX-s2b, SS-s2b, whose tests are on Server peers, use `symbolic_lor_server` with `½(ε_A2pub + ε_inj)`; mode P)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
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
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) ∘
          PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
            {true}).toReal) -
      ((𝒟[((fun outcome => happens (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
        setup.serverKeyId budget guess nbfFilter)
          outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => happens (lorEligEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          nbfFilter) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
            {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps bounded shortRejects (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailure NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (protectedBinding)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt IdentityCollision)
open PqxdhDeploymentHeadlineSymbolic (SymHandle)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest admissibleTest)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

/-- Production form of `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound` (frozen: `symbolic_lor` with CE-LOR's bound (`PqxdhDeploymentHeadlineLor.ce_lor` at the NoBundleFailure filter)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) ∘
          PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
            {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc)
                runtime fallback
              caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailure NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (protectedBinding)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt IdentityCollision)
open PqxdhDeploymentHeadlineSymbolic (SymHandle)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest admissibleTest)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

/-- Production form of `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server` (frozen: `symbolic_lor_server` (design-v2 section 7.5 restricted to Server-peer tests; VC rows SSX-s2b, SS-s2b on Server-side symbolic eligibility, mode P)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (guess : X → Bool) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(lorWinPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(lorEligPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) ∘
          PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
            {true}).toReal) -
      ((𝒟[((fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto
        (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget guess nbfFilter) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => happens (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto
          (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget nbfFilter) outcome) ∘
            PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
            {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks shortRejects (RawCtxFrameDecoding.sender reader.model)
      ensureInit ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) bounds adversary budget respects runtime
      guess identityFallback ordinaryFallback

end

section
open PqxdhDeploymentHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailure NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (protectedBinding)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt IdentityCollision)
open PqxdhDeploymentHeadlineSymbolic (SymHandle)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest admissibleTest)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

/-- Production form of `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server_bound` (frozen: `symbolic_lor_server` with CE-LOR's Server-side bound (`PqxdhDeploymentHeadlineLor.ce_lor_server` at the NoBundleFailure filter, no `β_g`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_server_bound (setup : Setup baseSpec KemSK)
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
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(lorWinPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(lorEligPeerSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) ∘
          PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds .P adversary).run
          runtime]
            {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto
              (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
              nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto
              (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
              nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
          recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
              fallback
            caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (PqxdhDeploymentHeadlineEvents.lorWinPeerEvent setup.source.crypto
                (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget guess
                nbfFilter) lorClaim (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto
                (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
              (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto
                (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                nbfFilter) lorClaim (g.1, g.2.castSucc) runtime) +
            recLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget (g.1, g.2.castSucc)
                runtime fallback
              caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (PqxdhDeploymentHeadlineEvents.lorEligPeerEvent setup.source.crypto
                  (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                  nbfFilter) lorClaim (g.1, g.2.castSucc))))) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_server_bound setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct bounds adversary budget respects
      runtime fallback guess identityFallback ordinaryFallback

end

section
open PqxdhDeploymentHeadlineInjective
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentHeadlineSymbolic (OriginFailureSym originSym)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim)
open PqxdhDeploymentHeadlineGap (a2pubTerm ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm)

/-- Production form of `PqxdhDeploymentHeadlineInjective.ce_or_injective_b2s` (frozen: `ce_or_injective_b2s` (design-v2 section 7.3; the injective L2-origin rows with CE-R1' and CE-C3)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(injectiveB2s setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      (RawCtxFrameDecoding.sender reader.model) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .b2s)
              (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineInjective.ce_or_injective_b2s setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack shortRejects bounds mode adversary budget respects runtime fallback identityFallback
      ordinaryFallback

end

section
open PqxdhDeploymentHeadlineInjective
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentHeadlineSymbolic (OriginFailureSym originSym)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim)
open PqxdhDeploymentHeadlineGap (a2pubTerm ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm)

/-- Production form of `PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b` (frozen: `ce_or_injective_s2b` (design-v2 section 7.3; the injective S2b-origin rows with CE-A1's injectivity and CE-C3, without the identity collision, which `ce_or_injective_s2b_full` adds at the same bound)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(injectiveS2b setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      (RawCtxFrameDecoding.sender reader.model) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      ENNReal.ofReal ((∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
          (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
          (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) a1Fallback
          signatureFallback) +
        ∑ target : Fin (budget.create + 1), (PqxdhJointIdentity.advantage setup.joint
          (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal) +
      ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineInjective
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentHeadlineSymbolic (OriginFailureSym originSym)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim)
open PqxdhDeploymentHeadlineGap (a2pubTerm ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm)

/-- Production form of `PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full` (frozen: `ce_or_injective_s2b_full` (design-v2 section 7.3; the injective S2b-origin rows with CE-A1's injectivity, the identity collision and CE-C3)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(injectiveS2bFull setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      (RawCtxFrameDecoding.sender reader.model) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (orClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      ENNReal.ofReal ((∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
          (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
          (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) a1Fallback
          signatureFallback) +
        ∑ target : Fin (budget.create + 1), (PqxdhJointIdentity.advantage setup.joint
          (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal) +
      ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section Terms
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)

/-- The explicit public ciphertext-gap term `PqxdhDeploymentHeadlineGap.ctGapTerm` of the F-ct2 forms at the production codec and route is the probability that the classical production source game ends with `CtGapEvent`, read back through `unwrap` (by its definition and `PqxdhDeploymentProductionTransfer.chance`). -/
theorem ctGapTerm_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    PqxdhDeploymentHeadlineGap.ctGapTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime =
      𝒟[((fun outcome => PqxdhDeploymentKemTransfer.happens
          (PqxdhDeploymentHeadlineGap.ctGapEvent setup.source.crypto
            (PqxdhBoundaryRecordPrelude.withReader codec reader)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} :=
  (PqxdhDeploymentProductionTransfer.chance setup codec reader erased checks ensureInit bounds mode adversary runtime
    _).symm

/-- The explicit public ciphertext-collision term `PqxdhDeploymentHeadlineCollision.ctCollTerm` of the P2 symbolic forms at the production codec and route is the probability that the classical production source game ends with `CtCollEvent`, read back through `unwrap` (by its definition and `PqxdhDeploymentProductionTransfer.chance`). -/
theorem ctCollTerm_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    PqxdhDeploymentHeadlineCollision.ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime =
      𝒟[((fun outcome => PqxdhDeploymentKemTransfer.happens
          (PqxdhDeploymentHeadlineCollision.ctCollEvent setup.source.crypto
            (PqxdhBoundaryRecordPrelude.withReader codec reader)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} :=
  (PqxdhDeploymentProductionTransfer.chance setup codec reader erased checks ensureInit bounds mode adversary runtime
    _).symm

end Terms

end BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_sum_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_world_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_world_close

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_world_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_world_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_s2b_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_s2b_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_sender_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_sender_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_sender' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_sender

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_server_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor_server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor_server_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_lor_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.server_gap_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.server_gap_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_a1_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_a1_linked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.sym_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.sym_gap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.identity_collision_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.identity_collision_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_b2s_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_b2s_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_s2b_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_s2b_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_uks_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_server_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_server_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_beacon_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_app_beacon_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_server_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_server_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_beacon_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_kt_beacon_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor_server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.symbolic_lor_server_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_injective_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_injective_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_injective_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_injective_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_injective_s2b_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ce_or_injective_s2b_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ctGapTerm_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ctGapTerm_source

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ctCollTerm_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical.ctCollTerm_source
