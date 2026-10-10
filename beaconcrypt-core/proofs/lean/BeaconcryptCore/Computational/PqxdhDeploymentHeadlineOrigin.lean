-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure

/-!
# CE-OR: record origin of the common deployment experiment (CE-12 P1, design-v2 section 4.2)

The headline CE-OR in both directions and every observation mode (VC rows L2-origin, b2s-C2, b2s-C2-chosen-fs, b2s-C4, far-b2s-C4 for b2s and S2b-origin, s2b-C1, s2b-C4, far-s2b-C4 for s2b, design-v2 section 12): the probability that the deployment experiment ends with an accepted raw receive in the direction, on a handle designated `g`, whose decoded frame the CE counterpart of the handle (`PqxdhDeploymentHeadlineEvents.cpart`) did not publish before (`PqxdhDeploymentHeadlineEvents.OriginFailure`) is at most the sum over the targets `g` in `Fin qAccept × Fin qCreate`, each with coefficient one, of

- b2s (`ce_or_b2s`, the Server receives): `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, with no anomaly term;
- s2b (`ce_or_s2b`, a Beacon owner receives): `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`.

`publicationTerm budget = 2·R·S/2^512` is the commitment-guessing term of `PqxdhRecordLiftIdeal.OriginStatement` (decision D2). The chain is C1-C6 (`chain_server`, `chain_beta`), C7 with the integrity record lift (`auth_le`: `PqxdhRecordLiftComposition.record_auth_lift` at the frame of `frame_idealD`), the containments `origin_b2s` and `origin_s2b`, and `PqxdhRecordFactsOriginClosure.origin_statement` in `idealAuth`. Per-target forms: `ce_or_b2s_target`, `ce_or_s2b_target`.

Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac`, `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, `FrameReadBack codec`, `DecoderAgreement route codec.frameRead` and `budget.Respects adversary`; the AEAD forgery fallback is a parameter of the integrity loss. Events are on decoded frames (`codec.frameRead`), raw-byte events are not contained. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin
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

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The unpublished-accept event on the record lift's view of `idealAuth` with the ideal environment of a target has probability at most `publicationTerm budget` (`PqxdhRecordFactsOriginClosure.origin_statement` at the frame of `frame_idealD`). -/
theorem unpublished_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (agreement : RawCtxServerRouting.DecoderAgreement route codec.frameRead) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRecordLiftIdeal.unpublishedEvent codec route <$> (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤ publicationTerm budget := by
  rw [Functor.map_map]
  exact (PqxdhRecordFactsOriginClosure.origin_statement setup codec route setup.serverKeyId bounds frameReadBack
    agreement (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (PqxdhDeploymentHeadlineChain.startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode adversary budget respects).2.2.1

/-- **CE-OR b2s, per target** (design-v2 section 4.2): the probability that the deployment experiment ends with a b2s origin failure whose first failing entry's receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`; no anomaly term. -/
theorem ce_or_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (agreement : RawCtxServerRouting.DecoderAgreement route codec.frameRead) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g) +
      publicationTerm budget := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects
    (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
    (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
      (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealAuth setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds mode adversary) _ _
    (PqxdhDeploymentHeadlineContain.origin_b2s setup codec budget route g)
  have final := unpublished_final setup codec checks route caps bounded ensureInit qInit initBound frameReadBack
    agreement bounds mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ ((publicationTerm budget +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (serverSlotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-OR b2s** (design-v2 section 4.2, `ce_or_b2s`): the probability that the deployment experiment ends with a b2s origin failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, each with coefficient one; no anomaly term. -/
theorem ce_or_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (agreement : RawCtxServerRouting.DecoderAgreement route codec.frameRead) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.origin_named setup.source.crypto codec setup.serverKeyId
      budget route .b2s)]
  exact Finset.sum_le_sum fun g _ => ce_or_b2s_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack agreement bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

/-- **CE-OR s2b, per target** (design-v2 section 4.2): the probability that the deployment experiment ends with an s2b origin failure whose first failing entry's receiving owner designates `g` is at most `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`. -/
theorem ce_or_s2b_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (agreement : RawCtxServerRouting.DecoderAgreement route codec.frameRead) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g) +
      publicationTerm budget := by
  have chain := PqxdhDeploymentHeadlineAnomaly.chain_beta setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects
    (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
    (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (slotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
      (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealAuth setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds mode adversary) _ _
    (PqxdhDeploymentHeadlineContain.origin_s2b setup codec budget route g)
  have final := unpublished_final setup codec checks route caps bounded ensureInit qInit initBound frameReadBack
    agreement bounds mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ (((publicationTerm budget +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (slotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g)) +
        beta setup codec route checks ensureInit bounds mode adversary budget g runtime) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) :=
        add_le_add (add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-OR s2b** (design-v2 section 4.2, `ce_or_s2b`): the probability that the deployment experiment ends with an s2b origin failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`, each with coefficient one. -/
theorem ce_or_s2b (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (agreement : RawCtxServerRouting.DecoderAgreement route codec.frameRead) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.origin_named setup.source.crypto codec setup.serverKeyId
      budget route .s2b)]
  exact Finset.sum_le_sum fun g _ => ce_or_s2b_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack agreement bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.unpublished_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.unpublished_final

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_s2b_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_s2b_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin.ce_or_s2b
