-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed

/-!
# CE-12 D-ct: closed forms of the P4 run-phase billed and closed headlines

CE-12 P4 (integrated at central `427758b6`) restates six run-phase forms that still carry the explicit public term `ctGapTerm` of the run-phase adversary `first`: the billed forms `ce_app_later_sym_billed`, `ce_app_beacon_later_sym_billed` and `symbolic_lor_later_bound_billed` of `PqxdhDeploymentLaterHeadlineGated`, and the forms `symbolic_lor_later_closed`, `symbolic_lor_later_bound_closed` and `symbolic_lor_later_bound_closed_billed` of `PqxdhDeploymentLaterHeadlineClosed`, whose `ctCollTerm` is already closed by `ε_ctcoll`. Each theorem `T_dct` of this module is the frozen `T` with `ctGapTerm setup codec checks route ensureInit bounds mode first runtime` replaced by `epsCt setup codec checks route ensureInit bounds mode first budget runtime` (`PqxdhDeploymentHeadlineDctEvent.epsCt`), proved as `T` followed by `PqxdhDeploymentHeadlineDctWorld.ctgap_term_le` at `first` under monotonicity (`gcongr`); every other term and every bills conjunct is unchanged. The three `symbolic_lor_later*_closed*_dct` forms carry neither `ctGapTerm` nor `ctCollTerm`: they are the fully closed run-phase LoR headlines.

The bills conjuncts of the four billed forms (`LaterTargetBills`, `A2Bills` where present, `A1Bills`, and in `symbolic_lor_later_bound_closed_billed_dct` also `InjBills` and `PairBills`) do not bill the attackers behind the KEM and slot reductions of `epsCt`: `LaterTargetBills` bills the run-phase compiled adversaries of `kemLossL` and `slotLossL`, while `epsCt` at `first` is made of `kemLoss` and `slotLoss` of the classical experiment of `first` at `(ctGapNamed, ctClaim)`. Those bills are `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`. The sibling `T_dct_full` of each of the four billed forms (`ce_app_later_sym_billed_dct_full`, `ce_app_beacon_later_sym_billed_dct_full`, `symbolic_lor_later_bound_billed_dct_full`, `symbolic_lor_later_bound_closed_billed_dct_full`) has the binders of `T_dct` and concludes the conclusion of `T_dct` word for word conjoined with that `TargetBills`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills` from premises that `T_dct` already has.

The premises are those of `T` plus those of `ctgap_term_le` that `T` lacks: `qInit` and `initBound` for `symbolic_lor_later_closed_dct`, none for the other five; each `T_dct_full` has the premises of its `T_dct`. No frozen theorem changes, and no `_dct` statement changes.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-! ### The closed forms of `PqxdhDeploymentLaterHeadlineGated` -/

section LaterHeadlineGated
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed selectedKem)
open PqxdhDeploymentLaterServerTransfer (decision)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentLaterServerCompile (compileServer)
open PqxdhDeploymentLaterServerCompileBudget (laterTransported)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentEnvironmentJoin (envReveal)
open PqxdhRecordLiftIdeal (View)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG)
open PqxdhDeploymentLaterHeadlineChain (inputL)
open PqxdhDeploymentHeadlineGuessBill (guessBill)
open PqxdhDeploymentLaterHeadlineApp
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhRecordLiftIdeal (ctxView)
open PqxdhRecordLiftLaterWorlds (laterIdealRecords)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)
open PqxdhDeploymentLaterHeadlineLor
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View publicHiding chainView ctxView)
open PqxdhRecordLiftLaterWorlds (laterRealChains laterIdealRecords)
open PqxdhDeploymentHeadlineChain (EnvG ServerSlots slotted serverSlotted chance_ne_top)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorWinPeerEvent lorEligPeerEvent lorClaim)
open PqxdhDeploymentHeadlineLor (hidingOf decisionHiding)
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentLaterHeadlineGated
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `ce_app_later_sym_billed_dct`: `PqxdhDeploymentLaterHeadlineGated.ce_app_later_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_later_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
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
    (𝒟[(fun outcome => appSym setup codec appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback := by
  have frozen := PqxdhDeploymentLaterHeadlineGated.ce_app_later_sym_billed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound shortRejects frameReadBack writable law spread
      adapter bounds first second budget respects post postRespects runtime fallback appClaim identityFallback
      ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2.1, frozen.2.2.2⟩

/-- `ce_app_later_sym_billed_dct_full`: `ce_app_later_sym_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`). The `LaterTargetBills` conjunct of `ce_app_later_sym_billed_dct` bills the run-phase compiled adversaries of `kemLossL` and `slotLossL`, not these. The binders, the bound and the other bills conjuncts are those of `ce_app_later_sym_billed_dct` word for word; no premise is added. -/
theorem ce_app_later_sym_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
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
    ((𝒟[(fun outcome => appSym setup codec appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime :=
  ⟨ce_app_later_sym_billed_dct setup functional codec checks route ensureInit phase1 phase2 correct caps bounded
      qInit initBound shortRejects frameReadBack writable law spread adapter bounds first second budget respects
      post postRespects runtime fallback appClaim identityFallback ordinaryFallback a1Fallback signatureFallback,
    PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
      initBound bounds .P first budget respects runtime fallback⟩

/-- `ce_app_beacon_later_sym_billed_dct`: `PqxdhDeploymentLaterHeadlineGated.ce_app_beacon_later_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_beacon_later_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(fun outcome => appOwnerSym setup appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback := by
  have frozen := PqxdhDeploymentLaterHeadlineGated.ce_app_beacon_later_sym_billed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      first second budget respects post postRespects runtime fallback appClaim a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

/-- `ce_app_beacon_later_sym_billed_dct_full`: `ce_app_beacon_later_sym_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`). The `LaterTargetBills` conjunct of `ce_app_beacon_later_sym_billed_dct` bills the run-phase compiled adversaries of `kemLossL` and `slotLossL`, not these. The binders, the bound and the other bills conjuncts are those of `ce_app_beacon_later_sym_billed_dct` word for word; no premise is added. -/
theorem ce_app_beacon_later_sym_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ((𝒟[(fun outcome => appOwnerSym setup appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime :=
  ⟨ce_app_beacon_later_sym_billed_dct setup functional codec checks route ensureInit phase1 phase2 correct caps
      bounded qInit initBound frameReadBack writable law spread adapter bounds first second budget respects post
      postRespects runtime fallback appClaim a1Fallback signatureFallback,
    PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
      initBound bounds .P first budget respects runtime fallback⟩

/-- `symbolic_lor_later_bound_billed_dct`: `PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_later_bound_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
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
    (ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
            runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
              runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  have frozen := PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed setup functional codec checks caps
      bounded shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first
      second budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit
      initBound post postRespects fallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2.1, frozen.2.2.2.1, frozen.2.2.2.2⟩

/-- `symbolic_lor_later_bound_billed_dct_full`: `symbolic_lor_later_bound_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`). The `LaterTargetBills` conjunct of `symbolic_lor_later_bound_billed_dct` bills the run-phase compiled adversaries of `kemLossL` and `slotLossL`, not these. The binders, the bound and the other bills conjuncts are those of `symbolic_lor_later_bound_billed_dct` word for word; no premise is added. -/
theorem symbolic_lor_later_bound_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
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
    ((ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
            runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
              runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime :=
  ⟨symbolic_lor_later_bound_billed_dct setup functional codec checks caps bounded shortRejects route ensureInit
      phase1 phase2 frameBack writable law spread correct adapter bounds first second budget respects runtime guess
      identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound post postRespects fallback,
    PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
      initBound bounds .P first budget respects runtime fallback⟩

end LaterHeadlineGated

/-! ### The closed forms of `PqxdhDeploymentLaterHeadlineClosed` -/

section LaterHeadlineClosed
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
open PqxdhDeploymentLaterHeadlineClosed
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `symbolic_lor_later_closed_dct`: `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `qInit`, `initBound`. -/
theorem symbolic_lor_later_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
            runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
              runtime] {true}).toReal) -
      ((𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
            runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
              runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  have frozen := PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed setup functional codec checks caps
      bounded shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first
      second budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact frozen.trans (by gcongr)

/-- `symbolic_lor_later_bound_closed_dct`: `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_later_bound_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
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
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
            runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
              runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  have frozen := PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed setup functional codec checks caps
      bounded shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first
      second budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit
      initBound post postRespects fallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact frozen.trans (by gcongr)

/-- `symbolic_lor_later_bound_closed_billed_dct`: `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_later_bound_closed_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
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
    (ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
            runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
              runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentLaterHeadlineGated.LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P
        first second budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  have frozen := PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed setup functional codec
      checks caps bounded shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter
      bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback
      qInit initBound post postRespects fallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

/-- `symbolic_lor_later_bound_closed_billed_dct_full`: `symbolic_lor_later_bound_closed_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`). The `LaterTargetBills` conjunct of `symbolic_lor_later_bound_closed_billed_dct` bills the run-phase compiled adversaries of `kemLossL` and `slotLossL`, not these. The binders, the bound and the other bills conjuncts are those of `symbolic_lor_later_bound_closed_billed_dct` word for word; no premise is added. -/
theorem symbolic_lor_later_bound_closed_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
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
    ((ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
            runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
              runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentLaterHeadlineGated.LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P
        first second budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime :=
  ⟨symbolic_lor_later_bound_closed_billed_dct setup functional codec checks caps bounded shortRejects route
      ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second budget respects
      runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound post postRespects
      fallback,
    PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit
      initBound bounds .P first budget respects runtime fallback⟩

end LaterHeadlineClosed

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct_full
