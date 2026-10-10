-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesClassical
import BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesLater
import BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainGated

/-!
# Production composition of items 3 and 7: the final production headlines

The final module of the production composition (the name pinned by the PB-D interface pin #415/#420); importing it imports the whole composition:

- `PqxdhDeploymentProductionTransfer`: the generic transfer lemmas (observation, distribution and Boolean-event transfer from the CE and LQ-F experiments at codec′ and route′ to the PB-D production source games at index 0, and the readings of the carried codec contracts at codec′).
- `PqxdhDeploymentProductionHeadlinesClassical`: production forms of the CE-12 P1 headlines (CE-KT, CE-OR, CE-UKS, CE-APP, CE-LOR and their per-target, summed, World and Server-side forms) and of the P2 gap, collision, symbolic, symbolic-LOR and injective forms, and the two explicit-term lemmas.
- `PqxdhDeploymentProductionHeadlinesLater`: production forms of the CE-12 P3 later-quantum headlines (CE-KT-L, CE-APP-L, CE-LOR-L and the later symbolic forms) and of P4 step 1 (their billed and closed forms); confidentiality only.
- This module: production forms of the CE-12 P2b billed, ciphertext-collision and closed forms (`ctCollTerm` replaced by `ctCollEps`), and of P4 steps 2 and 3 (AG lifts R1 and R2: the b2s Server pin and the mode-O plaintext rows of the design-v2 section 7.6 field table, with their origin-combined and billed forms).

Every theorem keeps the frozen theorem's name: the frozen statement instantiated at the production codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and route `route′ = RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment replaced by the probability of the same event, read back through `PqxdhBoundaryDeployment.unwrap`, on the classical production source game `PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 …` (`PqxdhDeploymentProductionTransfer.chance`). For `ct_collision_game`, `ct_coll_le` and `ct_coll_billed` the left side `ctCollTerm` is first unfolded to its definition. The bound and bills are the frozen ones, word for word at codec′ and route′. Premises: the frozen ones at codec′ and route′, except that `Phase1ReadBack` and `Phase2ReadBack` are stated at `codec` (`phase1_withReader`, `phase2_withReader`, `Iff.rfl`); `FrameReadBack` and `ReadWritable` are carried at codec′ exactly where the frozen theorem takes them. `ctGapTerm` stays explicit where the frozen form carries it (F-ct2; the D-ct closures are not on central and get production versions in a follow-up). No assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines

variable {ι KemSK Reader Response Message Root A X Out : Type} {baseSpec : OracleSpec ι}

section
open PqxdhDeploymentHeadlineGated
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

/-- Production form of `PqxdhDeploymentHeadlineGated.ce_app_target_billed` (frozen: `ce_app_target` (`PqxdhDeploymentHeadlineApp.ce_app_target`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_target_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => decide (happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
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
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_app_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim g

end

section
open PqxdhDeploymentHeadlineGated
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

/-- Production form of `PqxdhDeploymentHeadlineGated.ce_app_billed` (frozen: `ce_app` (`PqxdhDeploymentHeadlineApp.ce_app`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => happens (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_app_billed setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim

end

section
open PqxdhDeploymentHeadlineGated
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

/-- Production form of `PqxdhDeploymentHeadlineGated.ce_or_s2b_target_billed` (frozen: `ce_or_s2b_target` (`PqxdhDeploymentHeadlineOrigin.ce_or_s2b_target`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_target_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => decide (happens (originEvent setup.source.crypto
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
      publicationTerm budget) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_or_s2b_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlineGated
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

/-- Production form of `PqxdhDeploymentHeadlineGated.ce_or_s2b_billed` (frozen: `ce_or_s2b` (`PqxdhDeploymentHeadlineOrigin.ce_or_s2b`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => happens (originEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
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
          publicationTerm budget)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_or_s2b_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlineGated
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

/-- Production form of `PqxdhDeploymentHeadlineGated.ce_uks_sender_target_billed` (frozen: `ce_uks_sender_target` (`PqxdhDeploymentHeadlineUks.ce_uks_sender_target`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sender_target_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => decide (happens (uksSenderEvent setup.source.crypto
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
      bindingTerm (inputG caps qInit budget bounds)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_uks_sender_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlineGated
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

/-- Production form of `PqxdhDeploymentHeadlineGated.ce_uks_sender_billed` (frozen: `ce_uks_sender` (`PqxdhDeploymentHeadlineUks.ce_uks_sender`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sender_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => happens (uksSenderEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
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
          bindingTerm (inputG caps qInit budget bounds))) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_uks_sender_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlineGated
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
open PqxdhRecordLiftIdeal (ctxView idealRecords)
open PqxdhDeploymentHeadlineChain (EnvG)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_lor_target_billed` (frozen: `ce_lor_target` (`PqxdhDeploymentHeadlineLor.ce_lor_target`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_target_billed (setup : Setup baseSpec KemSK)
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
    (ENNReal.ofReal |(𝒟[((fun outcome => decide (happens (lorWinEvent setup.source.crypto
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
        checks ensureInit bounds .P adversary budget g runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_lor_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback guess filter g

end

section
open PqxdhDeploymentHeadlineGated
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
open PqxdhRecordLiftIdeal (ctxView idealRecords)
open PqxdhDeploymentHeadlineChain (EnvG)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_lor_billed` (frozen: `ce_lor` (`PqxdhDeploymentHeadlineLor.ce_lor`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_lor_billed (setup : Setup baseSpec KemSK)
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
    (ENNReal.ofReal |(𝒟[((fun outcome => happens (lorWinEvent setup.source.crypto
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
              runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_lor_billed setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback guess filter

end

section
open PqxdhDeploymentHeadlineGated
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed` (frozen: `ce_or_s2b_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(originSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
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
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineGated
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_uks_sym_billed` (frozen: `ce_uks_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_uks_sym`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(uksSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) ∘
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
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_uks_sym_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineGated
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_app_beacon_sym_billed` (frozen: `ce_app_beacon_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_sym_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(appOwnerSym setup appClaim ∘ PqxdhBoundaryDeployment.unwrap) <$>
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
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P adversary budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_app_beacon_sym_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineGated
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_app_sym_billed` (frozen: `ce_app_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_app_sym`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_sym_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim ∘ PqxdhBoundaryDeployment.unwrap) <$>
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
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P adversary budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_app_sym_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim
      identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineGated
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
open PqxdhDeploymentHeadlineEvents (LorElig)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed` (frozen: `symbolic_lor_bound` (`PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound_billed (setup : Setup baseSpec KemSK)
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
    (ENNReal.ofReal |((𝒟[(lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess ∘
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
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineGated
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

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed` (frozen: `ce_or_injective_s2b` (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(injectiveS2b setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
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
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineGated
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

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed` (frozen: `ce_or_injective_s2b_full` (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(injectiveS2bFull setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
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
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtColl
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentHeadlineCtGhost (gameG forget TripleColl)
open PqxdhDeploymentHeadlineCollision (ctCollTerm ctCollEvent pairCollision pairAdversary)
open PqxdhInitializerSecrecy (runtimeOfImpl kemAmbientImpl)
open OracleComp.EvalDist (expectedValue)

/-- Production form of `PqxdhDeploymentHeadlineCtColl.ct_collision_game` (frozen: `ct_collision_game` (design-v2 section 7.4)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The left side `ctCollTerm` of the frozen statement is unfolded to its definition (the probability of `ctCollEvent` on the CE experiment) before it is moved. -/
theorem ct_collision_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[((fun outcome => PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ((budget.create * budget.accept.choose 2 : Nat) : ℝ≥0∞) * pairCollision setup := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtColl.ct_collision_game setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) bounds mode adversary budget respects
      runtime

end

section
open PqxdhDeploymentHeadlineCtColl
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentHeadlineCtGhost (gameG forget TripleColl)
open PqxdhDeploymentHeadlineCollision (ctCollTerm ctCollEvent pairCollision pairAdversary)
open PqxdhInitializerSecrecy (runtimeOfImpl kemAmbientImpl)
open OracleComp.EvalDist (expectedValue)

/-- Production form of `PqxdhDeploymentHeadlineCtColl.ct_coll_le` (frozen: `ct_coll_le`). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The left side `ctCollTerm` of the frozen statement is unfolded to its definition (the probability of `ctCollEvent` on the CE experiment) before it is moved. -/
theorem ct_coll_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[((fun outcome => PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤ ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtColl.ct_coll_le setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) functional bounds mode adversary budget
      respects runtime

end

section
open PqxdhDeploymentHeadlineCtColl
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentHeadlineCtGhost (gameG forget TripleColl)
open PqxdhDeploymentHeadlineCollision (ctCollTerm ctCollEvent pairCollision pairAdversary)
open PqxdhInitializerSecrecy (runtimeOfImpl kemAmbientImpl)
open OracleComp.EvalDist (expectedValue)

/-- Production form of `PqxdhDeploymentHeadlineCtColl.ct_coll_billed` (frozen: `ct_coll_le` with the bill of its reduction). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The left side `ctCollTerm` of the frozen statement is unfolded to its definition (the probability of `ctCollEvent` on the CE experiment) before it is moved. -/
theorem ct_coll_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) :
    𝒟[((fun outcome => PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤ ctCollEps setup budget ∧
      (pairAdversary setup.kem).MakesAtMostQueries 0 0 0 caps.encapsUniform caps.encapsBase 0 := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtColl.ct_coll_billed setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) functional caps bounded bounds mode
      adversary budget respects runtime

end

section
open PqxdhDeploymentHeadlineCtClosed
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed` (frozen: `ce_or_s2b_sym` closed (`PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym_closed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed_billed` (frozen: `ce_or_s2b_sym` closed and billed (`PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed` with `ctCollTerm` replaced by `ε_ctcoll`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym_closed_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(originSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed` (frozen: `ce_uks_sym` closed (`PqxdhDeploymentHeadlineSymbolic.ce_uks_sym` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym_closed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed_billed` (frozen: `ce_uks_sym` closed and billed (`PqxdhDeploymentHeadlineGated.ce_uks_sym_billed` with `ctCollTerm` replaced by `ε_ctcoll`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym_closed_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(uksSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) ∘
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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
open PqxdhDeploymentHeadlineEvents (LorElig)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_closed` (frozen: `symbolic_lor` closed (`PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_closed (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.symbolic_lor_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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
open PqxdhDeploymentHeadlineEvents (LorElig)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed` (frozen: `symbolic_lor_bound` closed (`PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound_closed (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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
open PqxdhDeploymentHeadlineEvents (LorElig)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed_billed` (frozen: `symbolic_lor_bound` closed and billed (`PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed` with `ctCollTerm` replaced by `ε_ctcoll`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound_closed_billed (setup : Setup baseSpec KemSK)
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
    (ENNReal.ofReal |((𝒟[(lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess ∘
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed` (frozen: `ce_or_injective_s2b` closed (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_closed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed_billed` (frozen: `ce_or_injective_s2b` closed and billed (`PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed` with `ctCollTerm` replaced by `ε_ctcoll`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_closed_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(injectiveS2b setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed` (frozen: `ce_or_injective_s2b_full` closed (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full_closed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineCtClosed
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

open Classical in
/-- Production form of `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed_billed` (frozen: `ce_or_injective_s2b_full` closed and billed (`PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed` with `ctCollTerm` replaced by `ε_ctcoll`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full_closed_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[(injectiveS2bFull setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlinePin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn summarize buildOf)
open PqxdhDeploymentHeadlineEvents (firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePinInvariant (PinFacts)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePin.ce_pin_b2s_target` (frozen: **R1, per target** (design-v2 section 7.6, b2s Server pin)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_pin_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[((fun outcome => decide (happens (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model))
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (pinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model)) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model))
        (pinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model))
        (pinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model))
          (pinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model)) g) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePin.ce_pin_b2s_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn summarize buildOf)
open PqxdhDeploymentHeadlineEvents (firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePinInvariant (PinFacts)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePin.ce_pin_b2s` (frozen: **R1** (design-v2 section 7.6, b2s Server pin, `ce_pin_b2s`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_pin_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 229#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[((fun outcome => happens (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model))
            (pinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model))
            (pinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (pinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model))
              (pinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc))) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePin.ce_pin_b2s setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn summarize buildOf)
open PqxdhDeploymentHeadlineEvents (firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePinInvariant (PinFacts)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePin.ce_or_pin_b2s_target` (frozen: **CE-OR b2s with the Server pin field, per target** (design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_pin_b2s_target (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => decide (happens (originPinEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model))
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (originPinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (originPinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (originPinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (originPinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model))
          (originPinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) g) +
      publicationTerm budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePin.ce_or_pin_b2s_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn summarize buildOf)
open PqxdhDeploymentHeadlineEvents (firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePinInvariant (PinFacts)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePin.ce_or_pin_b2s` (frozen: **CE-OR b2s with the Server pin field** (`ce_or_pin_b2s`, design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_pin_b2s (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (originPinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (originPinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model))
            (originPinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originPinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model))
              (originPinClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePin.ce_or_pin_b2s setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_plain_b2s_target` (frozen: **R2 b2s, per target** (design-v2 section 7.6, mode-O plaintext, b2s)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_b2s_target (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => decide (happens (plainEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .b2s)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s) g runtime) +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s)
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s) g) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_plain_b2s_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_plain_b2s` (frozen: **R2 b2s** (`ce_plain_b2s`, design-v2 section 7.6, mode-O plaintext, b2s)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_b2s (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .b2s) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s)
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc))) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_plain_b2s setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_plain_s2b_target` (frozen: **R2 s2b, per target** (design-v2 section 7.6, mode-O plaintext, s2b)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_s2b_target (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => decide (happens (plainEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .s2b)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds mode adversary budget g runtime +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b)
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) g) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_plain_s2b_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_plain_s2b` (frozen: **R2 s2b** (`ce_plain_s2b`, design-v2 section 7.6, mode-O plaintext, s2b)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_s2b (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b)
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc))) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_plain_s2b setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s_target` (frozen: **CE-OR b2s with the plaintext field, per target** (design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_plain_b2s_target (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => decide (happens (originPlainEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .b2s)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .b2s) outcome = some g)) ∘
              PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .b2s)
        (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .b2s) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .b2s)
        (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .b2s) g runtime) +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)
            .b2s)
          (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .b2s) g) +
      publicationTerm budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s` (frozen: **CE-OR b2s with the plaintext field** (`ce_or_plain_b2s`, design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_plain_b2s (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .b2s)
        outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc)
                runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc)
                runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
            (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model) .b2s)
              (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b_target` (frozen: **CE-OR s2b with the plaintext field, per target** (design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_plain_s2b_target (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => decide (happens (originPlainEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .s2b)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .s2b) outcome = some g)) ∘
              PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b)
        (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b)
        (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds mode adversary budget g runtime +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .s2b)
          (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .s2b) g) +
      publicationTerm budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b` (frozen: **CE-OR s2b with the plaintext field** (`ce_or_plain_s2b`, design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_plain_s2b (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b)
        outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)
                runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)
                runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
            (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_plain_every_b2s` (frozen: **R2 b2s with every production** (the reading of design-v2 section 7.6 in which the returned plaintext differs from every counterpart production of the frame and one exists)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_every_b2s (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (plainEveryEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .b2s) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s)
            (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
            (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .b2s)
              (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .b2s) (g.1, g.2.castSucc))) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_plain_every_b2s setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_plain_every_s2b` (frozen: **R2 s2b with every production**). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_every_s2b (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (plainEveryEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
            (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc))) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_plain_every_s2b setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s_target` (frozen: **CE-OR b2s with every computational field, per target** (design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_fields_b2s_target (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => decide (happens (originFieldsEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model))
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (originFieldsClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originFieldsEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (originFieldsClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originFieldsEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model))
        (originFieldsClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model)) g runtime) +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (originFieldsEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model))
          (originFieldsClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model)) g) +
      publicationTerm budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s_target setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s` (frozen: **CE-OR b2s with every computational field** (`ce_or_fields_b2s`, design-v2 sections 4.2 and 7.6)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_fields_b2s (setup : Setup baseSpec KemSK)
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
    𝒟[((fun outcome => happens (originFieldsEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originFieldsEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model))
            (originFieldsClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originFieldsEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model))
            (originFieldsClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
              setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc) runtime) +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
            (serverSlotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originFieldsEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget
                (RawCtxFrameDecoding.sender reader.model))
              (originFieldsClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model)) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlainGated
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_target_billed` (frozen: `ce_plain_s2b_target` (`PqxdhDeploymentHeadlinePlain.ce_plain_s2b_target`, R2 s2b per target: `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_s2b_target_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => decide (happens (plainEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .s2b)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) outcome = some g)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds mode adversary budget g runtime +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b)
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) g)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePlainGated
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_billed` (frozen: `ce_plain_s2b` (`PqxdhDeploymentHeadlinePlain.ce_plain_s2b`, R2 s2b: the sum over the targets of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_s2b_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => happens (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
      setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b)
        (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
          (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b)
          (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)))) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlainGated.ce_plain_s2b_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlainGated
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_target_billed` (frozen: `ce_or_plain_s2b_target` (`PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b_target`, CE-OR s2b with the plaintext field per target: `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`, with `kemLoss`, `slotLoss` and `authLoss_g` at the combined event and claim; `β_g`, which depends only on the target, and `publicationTerm budget` are the same terms as in `ce_or_s2b`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_plain_s2b_target_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => decide (happens (originPlainEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
        (RawCtxFrameDecoding.sender reader.model) .s2b)
        outcome = true ∧ designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
          setup.serverKeyId budget
          (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .s2b) outcome = some g)) ∘
              PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b)
        (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b)
        (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
          budget (RawCtxFrameDecoding.sender reader.model) .s2b) g runtime) +
      beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) checks
        ensureInit bounds mode adversary budget g runtime +
      authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .s2b)
          (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget (RawCtxFrameDecoding.sender reader.model) .s2b) g) +
      publicationTerm budget) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_target_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback g

end

section
open PqxdhDeploymentHeadlinePlainGated
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_billed` (frozen: `ce_or_plain_s2b` (`PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b`, CE-OR s2b with the plaintext field: the sum over the targets of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`, with `kemLoss`, `slotLoss` and `authLoss_g` at the combined event and claim; `β_g`, which depends only on the target, and `publicationTerm budget` are the same terms as in `ce_or_s2b`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_plain_s2b_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => happens (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b)
        outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)
                runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)
                runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
            (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (originPlainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (originPlainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlainGated.ce_or_plain_s2b_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

section
open PqxdhDeploymentHeadlinePlainGated
open PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

/-- Production form of `PqxdhDeploymentHeadlinePlainGated.ce_plain_every_s2b_billed` (frozen: `ce_plain_every_s2b` (`PqxdhDeploymentHeadlinePlain.ce_plain_every_s2b`, R2 s2b with every production: the bound of `ce_plain_s2b`) with its bills). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); the same bound (every other term at the production codec and route). The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_plain_every_s2b_billed (setup : Setup baseSpec KemSK)
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
    (𝒟[((fun outcome => happens (plainEveryEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
      reader) setup.serverKeyId budget (RawCtxFrameDecoding.sender reader.model) .s2b) outcome) ∘
        PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b)
            (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model)
            checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget (g.1, g.2.castSucc)
              runtime
              fallback caps qInit
            (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (plainEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b)
              (plainClaim setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget (RawCtxFrameDecoding.sender reader.model) .s2b) (g.1, g.2.castSucc)))) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlinePlainGated.ce_plain_every_s2b_billed setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback

end

end BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sender_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sender_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sender_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sender_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_lor_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_lor_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_lor_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_lor_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_beacon_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_beacon_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_app_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_bound_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_bound_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_full_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_full_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ct_collision_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ct_collision_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ct_coll_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ct_coll_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ct_coll_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ct_coll_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_sym_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_sym_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_sym_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_s2b_sym_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sym_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sym_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sym_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_uks_sym_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_bound_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_bound_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_bound_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.symbolic_lor_bound_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_full_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_full_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_full_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_injective_s2b_full_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_pin_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_pin_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_pin_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_pin_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_pin_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_pin_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_pin_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_pin_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_every_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_every_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_every_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_every_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_fields_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_fields_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_fields_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_fields_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_or_plain_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_every_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlines.ce_plain_every_s2b_billed
