-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal

/-!
# CE-UKS: no unknown-key share between record handles (CE-12 P1, design-v2 section 4.3)

The headline CE-UKS in every observation mode (VC row b2s-UKSr, design-v2 section 12), on decoded frames:

- Receiver side (`ce_uks_b2s`, the CE form of b2s-UKSr): the probability that the deployment experiment ends with an accepted raw receive on a Server peer designated `g`, of a decoded frame that some handle other than the peer's CE partner returned anywhere in the transcript (`PqxdhDeploymentHeadlineEvents.UksReceiverFailure`), is at most the sum over the targets `g` in `Fin qAccept × Fin qCreate`, each with coefficient one, of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + bindingTerm BI_g`, with no anomaly term.
- Sender side (`ce_uks_sender`, used by the symbolic UKS corollary of unit P2): an owner designated `g` returned a record whose decoded frame some raw receive accepted on a handle other than the owner's CE partner (`UksSenderFailure`); the same bound with `β_g` added and `IS_g` in place of `ISs_g`.

`bindingTerm BI_g = (R + S + H)·S/2^512` with `H = sharedHashTotal BI_g` is the cross-handle term of `PqxdhRecordLiftIdeal.BindingTarget`, at the bill input `BI_g` of the frame of `frame_idealD`. The chain is C1-C6 (`chain_server`, `chain_beta`), C7 with the integrity record lift (`auth_le`), the containments `uks_receiver` and `uks_sender` (`CrossAccept`), and `PqxdhRecordFactsBindingGlobal.bindingTarget` in `idealAuth`. Per-target forms: `ce_uks_b2s_target`, `ce_uks_sender_target`. No sender binding is used: every Server peer seals with the Server key ID, so the bound rests on the private commitments of the ideal CTX worlds.

Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac`, `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, `FrameReadBack codec` and `budget.Respects adversary`; the AEAD forgery fallback is a parameter of the integrity loss. The plaintext-linked UKS form has no CE event and is not claimed (design-v2 section 15). No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks
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

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The cross-accept event on the record lift's view of `idealAuth` with the ideal environment of a target has probability at most `bindingTerm BI_g` (`PqxdhRecordFactsBindingGlobal.bindingTarget` at the frame of `frame_idealD`). -/
theorem cross_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRecordLiftIdeal.crossEvent codec route <$> (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤ bindingTerm (inputG caps qInit budget bounds) := by
  rw [Functor.map_map]
  exact (PqxdhRecordFactsBindingGlobal.bindingTarget setup codec route setup.serverKeyId bounds frameReadBack
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    (PqxdhDeploymentHeadlineChain.startupG caps qInit budget) (allowanceG (baseAllowance caps) ceFirstTouch)
    (PqxdhDeploymentIdealFrame.frame_idealD setup codec checks caps bounded (Target.ofCE budget g) ensureInit qInit
      initBound 0 runtime) mode adversary budget respects).1

/-- **CE-UKS, receiver side, per target** (design-v2 section 4.3): the probability that the deployment experiment ends with a receiver-side UKS failure whose first witness entry's receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + bindingTerm BI_g`; no anomaly term. -/
theorem ce_uks_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
        (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
        (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
          (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g) +
      bindingTerm (inputG caps qInit budget bounds) := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects
    (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
    (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
      (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealAuth setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds mode adversary) _ _
    (PqxdhDeploymentHeadlineContain.uks_receiver setup codec budget route g)
  have final := cross_final setup codec checks route caps bounded ensureInit qInit initBound frameReadBack bounds
    mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ ((bindingTerm (inputG caps qInit budget bounds) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (serverSlotted setup codec budget (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
              (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
          (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
          (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-UKS, receiver side** (design-v2 section 4.3, the CE form of b2s-UKSr): the probability that the deployment experiment ends with a receiver-side UKS failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + bindingTerm BI_g`, each with coefficient one; no anomaly term. -/
theorem ce_uks_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
            (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
            (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
              (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc)) +
          bindingTerm (inputG caps qInit budget bounds)) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.uksReceiver_named setup.source.crypto codec
      setup.serverKeyId budget route)]
  exact Finset.sum_le_sum fun g _ => ce_uks_b2s_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

/-- **CE-UKS, sender side, per target** (design-v2 section 4.3): the probability that the deployment experiment ends with a sender-side UKS failure whose first witness entry's sending owner designates `g` is at most `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + bindingTerm BI_g`. -/
theorem ce_uks_sender_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
        (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
        (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
          (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g) +
      bindingTerm (inputG caps qInit budget bounds) := by
  have chain := PqxdhDeploymentHeadlineAnomaly.chain_beta setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects
    (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
    (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (slotted setup codec budget (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
      (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g)
  have hit := PqxdhDeploymentHeadlineContain.chance_mono
    (ctxView <$> idealAuth setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
      setup.serverKeyId bounds mode adversary) _ _
    (PqxdhDeploymentHeadlineContain.uks_sender setup codec budget route g)
  have final := cross_final setup codec checks route caps bounded ensureInit qInit initBound frameReadBack bounds
    mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ (((bindingTerm (inputG caps qInit budget bounds) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (slotted setup codec budget (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
              (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g)) +
        beta setup codec route checks ensureInit bounds mode adversary budget g runtime) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
          (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
          (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) :=
        add_le_add (add_le_add (add_le_add (lift.trans (add_le_add (hit.trans final) le_rfl)) le_rfl) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-UKS, sender side** (design-v2 section 4.3, `ce_uks_sender`): the probability that the deployment experiment ends with a sender-side UKS failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + bindingTerm BI_g`, each with coefficient one. -/
theorem ce_uks_sender (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
            (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
            (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
              (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc)) +
          bindingTerm (inputG caps qInit budget bounds)) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (PqxdhDeploymentHeadlineEvents.uksSender_named setup.source.crypto codec
      setup.serverKeyId budget route)]
  exact Finset.sum_le_sum fun g _ => ce_uks_sender_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.cross_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.cross_final

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_sender_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_sender_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_sender' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks.ce_uks_sender
