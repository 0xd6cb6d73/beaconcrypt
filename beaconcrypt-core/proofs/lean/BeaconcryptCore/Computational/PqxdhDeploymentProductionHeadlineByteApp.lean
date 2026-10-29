-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineByteApp
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineByteApp
import BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer

/-!
# Byte-accurate fresh-message bounds on the production source games

The summed CE-APP and later-disclosure CE-APP-L bounds are transported through the existing exact source-game equalities. Their final guessing term is `256^-min` for each target; every other loss and carried codec/primitive premise is unchanged. These are the existing logical production boundary, with its explicit codec contracts; they do not discharge the current raw-CBOR or mandatory-ML composition obligations.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp
variable {ι KemSK Reader Response Message Root A X Out : Type} {baseSpec : OracleSpec ι}

section
open PqxdhDeploymentHeadlineByteApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)

/-- Production-source form of the byte-accurate `PqxdhDeploymentHeadlineByteApp.ce_app` bound. -/
theorem ce_app (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simpa only [PqxdhDeploymentProductionTransfer.chance] using
    PqxdhDeploymentHeadlineByteApp.ce_app setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim

end

section
open PqxdhDeploymentHeadlineByteApp
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)

/-- Production-source form of the byte-accurate `PqxdhDeploymentHeadlineByteApp.ce_app_server` bound. -/
theorem ce_app_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simpa only [PqxdhDeploymentProductionTransfer.chance] using
    PqxdhDeploymentHeadlineByteApp.ce_app_server setup functional (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds adversary budget respects runtime fallback appClaim

end

section
open PqxdhDeploymentLaterHeadlineByteApp
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

/-- Production-source form of the byte-accurate `PqxdhDeploymentLaterHeadlineByteApp.ce_app_later` bound. -/
theorem ce_app_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simpa only [PqxdhDeploymentProductionTransfer.chance_later] using
    PqxdhDeploymentLaterHeadlineByteApp.ce_app_later setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim

end

section
open PqxdhDeploymentLaterHeadlineByteApp
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

/-- Production-source form of the byte-accurate `PqxdhDeploymentLaterHeadlineByteApp.ce_app_server_later` bound. -/
theorem ce_app_server_later (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
          ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹) := by
  simpa only [PqxdhDeploymentProductionTransfer.chance_later] using
    PqxdhDeploymentLaterHeadlineByteApp.ce_app_server_later setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      bounds first second budget respects post postRespects runtime fallback appClaim

end

end BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app_later

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlineByteApp.ce_app_server_later
