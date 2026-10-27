-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective

/-!
# The CE-12 headlines with `β_g`, billed (CE-12 P2b, design-v2 section 9)

The CE-12 headlines whose bound carries the anomaly term `β_g` cite the IND-CCA advantage of the predict-then-compare adversary `ptc` built from CE-11b's anomaly guesser. Until P2b its phase-1 uniform bill (`guessBill`) was not proved, so these headlines were gated on it (guide "CE-12 P2: open points", item 1 (c)). Each theorem below restates one of them unchanged and conjoins the bills of the reductions behind its terms, proved at the deployment budget from resource premises the headline already takes (`PqxdhDeploymentHeadlineBillsFull`):

- P1 (per target and summed): `ce_app_target_billed`, `ce_app_billed`, `ce_or_s2b_target_billed`, `ce_or_s2b_billed`, `ce_uks_sender_target_billed`, `ce_uks_sender_billed`, `ce_lor_target_billed`, `ce_lor_billed`, each with `TargetBills` (`kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g`, `recLoss_g`).
- P2: `ce_or_s2b_sym_billed`, `ce_uks_sym_billed` and `ce_app_beacon_sym_billed` with `TargetBills` and `A1Bills` (`ε_A1`); `ce_app_sym_billed` with `TargetBills`, `A2Bills` (`ε_A2pub`) and `A1Bills`; `symbolic_lor_bound_billed` with `TargetBills`, `A2Bills`, `A1Bills` and `InjBills` (`ε_inj`); `ce_or_injective_s2b_billed` and `ce_or_injective_s2b_full_billed` with `TargetBills`, `A1Bills` and `InjBills` (the terms of `ε_A1inj`).
- `anomaly_beta_billed`: `PqxdhDeploymentHeadlineAnomaly.anomaly_beta` with `ptc_bills`; it adds the resource premises of `ptc_bills` (`KemBound`, `initBound` and `budget.Respects adversary`) to those of `anomaly_beta`.

The terms `ctGapTerm` and `ctCollTerm` are probabilities in the real experiment, not advantages of reductions, so they have no bill; the forms that carry them keep them explicit, as P2 does (F-ct2 and the explicit `ctCollTerm`). The bounds are the frozen theorems' own, with the same premises; for the fifteen headline forms the bill conjuncts add no premise beyond those the headline already takes (`KemBound`, `initBound`, the budget and `SourceFullCorrect`). No assumption is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

section Anomaly
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (Anomaly)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineAnomaly (beta ptc)

open Classical in
/-- `anomaly_beta` with `β_g`'s bill: the Beacon-side anomaly of the target of `g` on the record world with its ideal environment has probability at most `β_g` (`PqxdhDeploymentHeadlineAnomaly.anomaly_beta`), and the predict-then-compare adversary whose IND-CCA advantage `β_g` cites makes, before the challenge, at most `guessBill caps qInit budget bounds` uniform queries, no base-oracle query and at most `budget.finish + 1` decapsulations, and after the challenge none (`PqxdhDeploymentHeadlineGuessBill.ptc_bills`). -/
theorem anomaly_beta_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (caps : KemCaps) (bounded : KemBound setup caps)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧
        Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary] {true} ≤
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime ∧
    (ptc setup.kem (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec route checks (Target.ofCE budget g)
      ensureInit 0 runtime bounds mode adversary)).MakesAtMostQueries
        (PqxdhDeploymentHeadlineGuessBill.guessBill caps qInit budget bounds) 0 (budget.finish + 1) 0 0 0 :=
  ⟨PqxdhDeploymentHeadlineAnomaly.anomaly_beta setup functional codec checks route ensureInit phase1 phase2 bounds mode
    adversary budget g runtime,
   PqxdhDeploymentHeadlineGuessBill.ptc_bills setup codec route checks caps bounded ensureInit qInit initBound bounds mode
    adversary budget respects g runtime⟩

end Anomaly

section App
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

/-- `ce_app_target` (`PqxdhDeploymentHeadlineApp.ce_app_target`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_app_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (g : Fin budget.accept × Fin budget.capacity) :
    (𝒟[(fun outcome => decide (happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome =
        true ∧ designated setup.source.crypto codec setup.serverKeyId budget (appHandle appClaim) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
        (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
        (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim) g runtime) +
      beta setup codec route checks ensureInit bounds .P adversary budget g runtime +
      recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
          (appHandle appClaim) g) +
      ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime :=
  ⟨PqxdhDeploymentHeadlineApp.ce_app_target setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound bounds adversary budget respects runtime fallback appClaim g,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects runtime fallback⟩

/-- `ce_app` (`PqxdhDeploymentHeadlineApp.ce_app`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_app_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    (𝒟[(fun outcome => happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime :=
  ⟨PqxdhDeploymentHeadlineApp.ce_app setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound bounds adversary budget respects runtime fallback appClaim,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects runtime fallback⟩

end App

section Origin
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

/-- `ce_or_s2b_target` (`PqxdhDeploymentHeadlineOrigin.ce_or_s2b_target`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_or_s2b_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    (𝒟[(fun outcome => decide (happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
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
      publicationTerm budget) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlineOrigin.ce_or_s2b_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback g,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

/-- `ce_or_s2b` (`PqxdhDeploymentHeadlineOrigin.ce_or_s2b`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_or_s2b_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome) <$>
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
          publicationTerm budget)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlineOrigin.ce_or_s2b setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

end Origin

section Uks
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

/-- `ce_uks_sender_target` (`PqxdhDeploymentHeadlineUks.ce_uks_sender_target`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_uks_sender_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (g : Fin budget.accept × Fin budget.capacity) :
    (𝒟[(fun outcome => decide (happens (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
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
      bindingTerm (inputG caps qInit budget bounds)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlineUks.ce_uks_sender_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback g,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

/-- `ce_uks_sender` (`PqxdhDeploymentHeadlineUks.ce_uks_sender`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_uks_sender_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (𝒟[(fun outcome => happens (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route) outcome) <$>
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
          bindingTerm (inputG caps qInit budget bounds))) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime :=
  ⟨PqxdhDeploymentHeadlineUks.ce_uks_sender setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects runtime fallback⟩

end Uks

section Lor
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
/-- `ce_lor_target` (`PqxdhDeploymentHeadlineLor.ce_lor_target`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_lor_target_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) :
    (ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget
          guess filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => decide (happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget
          filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
          lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
          (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
            lorClaim g)) +
      2⁻¹ * beta setup codec route checks ensureInit bounds .P adversary budget g runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime :=
  ⟨PqxdhDeploymentHeadlineLor.ce_lor_target setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound bounds adversary budget respects runtime fallback guess filter g,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects runtime fallback⟩

open Classical in
/-- `ce_lor` (`PqxdhDeploymentHeadlineLor.ce_lor`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_lor_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    (ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess
          filter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime :=
  ⟨PqxdhDeploymentHeadlineLor.ce_lor setup functional codec checks route ensureInit phase1 phase2 correct caps
    bounded qInit initBound bounds adversary budget respects runtime fallback guess filter,
   PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects runtime fallback⟩

end Lor

section Symbolic
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
/-- `ce_or_s2b_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), the CE-A1 bills (`A1Bills`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_or_s2b_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[originSym setup codec route .s2b <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
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
          publicationTerm budget)) +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback :=
  ⟨PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget respects
    runtime fallback a1Fallback signatureFallback,
   ⟨PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
     initBound bounds mode adversary budget respects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds mode adversary budget
     respects a1Fallback signatureFallback⟩⟩

open Classical in
/-- `ce_uks_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_uks_sym`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), the CE-A1 bills (`A1Bills`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_uks_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[uksSym setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
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
          bindingTerm (inputG caps qInit budget bounds))) +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback :=
  ⟨PqxdhDeploymentHeadlineSymbolic.ce_uks_sym setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget respects
    runtime fallback a1Fallback signatureFallback,
   ⟨PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
     initBound bounds mode adversary budget respects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds mode adversary budget
     respects a1Fallback signatureFallback⟩⟩

open Classical in
/-- `ce_app_beacon_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), the CE-A1 bills (`A1Bills`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_app_beacon_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[appOwnerSym setup appClaim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback :=
  ⟨PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds adversary budget respects
    runtime fallback appClaim a1Fallback signatureFallback,
   ⟨PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
     initBound bounds .P adversary budget respects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds .P adversary budget
     respects a1Fallback signatureFallback⟩⟩

end Symbolic

section Symbolic
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
/-- `ce_app_sym` (`PqxdhDeploymentHeadlineSymbolic.ce_app_sym`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), the CE-A2pub bills (`A2Bills`), the CE-A1 bills (`A1Bills`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_app_sym_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[appSym setup codec appClaim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback :=
  ⟨PqxdhDeploymentHeadlineSymbolic.ce_app_sym setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound shortRejects frameReadBack writable law spread adapter bounds adversary budget
    respects runtime fallback appClaim identityFallback ordinaryFallback a1Fallback signatureFallback,
   ⟨PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
     initBound bounds .P adversary budget respects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a2_bills_all setup codec checks route caps bounded ensureInit qInit initBound
     bounds .P adversary budget respects runtime identityFallback ordinaryFallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds .P adversary budget
     respects a1Fallback signatureFallback⟩⟩

end Symbolic

section SymbolicLor
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
/-- `symbolic_lor_bound` (`PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), the CE-A2pub bills (`A2Bills`), the CE-A1 bills (`A1Bills`), the identity-collision bills (`InjBills`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem symbolic_lor_bound_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (ENNReal.ofReal |((𝒟[lorWinSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget :=
  ⟨PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound setup functional codec checks caps bounded shortRejects
    route ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct adapter bounds adversary
    budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback signatureFallback,
   ⟨PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
     initBound bounds .P adversary budget respects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a2_bills_all setup codec checks route caps bounded ensureInit qInit initBound
     bounds .P adversary budget respects runtime identityFallback ordinaryFallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds .P adversary budget
     respects a1Fallback signatureFallback,
    PqxdhDeploymentHeadlineBillsFull.inj_bills setup budget⟩⟩

end SymbolicLor

section Injective
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
/-- `ce_or_injective_s2b` (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), the CE-A1 bills (`A1Bills`), the identity-collision bills (`InjBills`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_or_injective_s2b_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[injectiveS2b setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
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
          publicationTerm budget)) +
      ENNReal.ofReal ((∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
          (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
          (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
          (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) a1Fallback
          signatureFallback) +
        ∑ target : Fin (budget.create + 1), (PqxdhJointIdentity.advantage setup.joint
          (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget :=
  ⟨PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback,
   ⟨PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
     initBound bounds mode adversary budget respects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds mode adversary budget
     respects a1Fallback signatureFallback,
    PqxdhDeploymentHeadlineBillsFull.inj_bills setup budget⟩⟩

open Classical in
/-- `ce_or_injective_s2b_full` (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full`) with its bills: the same bound, together with the per-target bills (`TargetBills`: `kemLoss`, `slotLoss`, `β_g` through `ptc_bills`, `authLoss_g` and `recLoss_g`), the CE-A1 bills (`A1Bills`), the identity-collision bills (`InjBills`), so that every advantage term of the bound, including `β_g`, cites a reduction whose query caps are proved at the deployment budget. -/
theorem ce_or_injective_s2b_full_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds)
    (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget)
    (respects : budget.Respects adversary)
    (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[injectiveS2bFull setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
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
          publicationTerm budget)) +
      ENNReal.ofReal ((∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
          (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
          (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
          (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) a1Fallback
          signatureFallback) +
        ∑ target : Fin (budget.create + 1), (PqxdhJointIdentity.advantage setup.joint
          (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget :=
  ⟨PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback,
   ⟨PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
     initBound bounds mode adversary budget respects runtime fallback,
    PqxdhDeploymentHeadlineBillsFull.a1_bills_all setup codec checks caps bounded route bounds mode adversary budget
     respects a1Fallback signatureFallback,
    PqxdhDeploymentHeadlineBillsFull.inj_bills setup budget⟩⟩

end Injective

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.anomaly_beta_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.anomaly_beta_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_s2b_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_s2b_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_uks_sender_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_uks_sender_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_uks_sender_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_uks_sender_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_lor_target_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_lor_target_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_lor_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_lor_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_uks_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_uks_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_beacon_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_beacon_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_sym_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_app_sym_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed
