-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor

/-!
# CE-12 D-ct: closed forms of the run-phase (later) headlines

The frozen run-phase (later) CE-12 headlines of `PqxdhDeploymentLaterHeadlineSymbolic` and `PqxdhDeploymentLaterHeadlineSymbolicLor` (P3) bound their events with the explicit public term `ctGapTerm` of the run-phase adversary `first`. Each theorem `T_dct` of this module is the frozen `T` with `ctGapTerm setup codec checks route ensureInit bounds mode first runtime` replaced by `epsCt setup codec checks route ensureInit bounds mode first budget runtime` (`PqxdhDeploymentHeadlineDctEvent.epsCt`), proved as `T` followed by `PqxdhDeploymentHeadlineDctWorld.ctgap_term_le` at `first` (whose `respects : budget.Respects first` is a premise of `T`) under monotonicity (`gcongr`); every other term, including `ctCollTerm` where the frozen form carries it, is unchanged.

The premises are those of `T` plus those of `ctgap_term_le` that `T` lacks: `qInit` and `initBound` for `ce_kt_later_sym_dct` and `ce_kt_beacon_later_sym_dct`; `FunctionalDecapsulation`, `qInit` and `initBound` for `symbolic_lor_later_dct`; none for the other three. No frozen theorem changes. The six run-phase forms that P4 adds (`PqxdhDeploymentLaterHeadlineGated`, `PqxdhDeploymentLaterHeadlineClosed`) are not on central and are not closed here.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-! ### The closed forms of `PqxdhDeploymentLaterHeadlineSymbolic` -/

section LaterHeadlineSymbolic
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
open PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `ce_app_later_sym_dct`: `PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_later_sym_dct (setup : Setup baseSpec KemSK)
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
    𝒟[(fun outcome => appSym setup codec appClaim (asClassical outcome)) <$>
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
        epsCt setup codec checks route ensureInit bounds .P first budget runtime) := by
  have frozen := PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound shortRejects frameReadBack writable law spread adapter bounds
      first second budget respects post postRespects runtime fallback appClaim identityFallback ordinaryFallback
      a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_app_beacon_later_sym_dct`: `PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_beacon_later_sym_dct (setup : Setup baseSpec KemSK)
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
    𝒟[(fun outcome => appOwnerSym setup appClaim (asClassical outcome)) <$>
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
        epsCt setup codec checks route ensureInit bounds .P first budget runtime) := by
  have frozen := PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      first second budget respects post postRespects runtime fallback appClaim a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_kt_later_sym_dct`: `PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `qInit`, `initBound`. -/
theorem ce_kt_later_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[(fun outcome => ktSym setup codec event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup codec checks route ensureInit bounds mode first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds mode first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds mode first budget runtime) := by
  have frozen := PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded shortRejects frameReadBack writable law spread adapter bounds mode first
      second budget respects post postRespects event claim runtime identityFallback ordinaryFallback a1Fallback
      signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode first budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_kt_beacon_later_sym_dct`: `PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `qInit`, `initBound`. -/
theorem ce_kt_beacon_later_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[(fun outcome => ktOwnerSym setup event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds mode first budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds mode first budget runtime) := by
  have frozen := PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded frameReadBack writable law spread adapter bounds mode first second
      budget respects post postRespects event claim runtime a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode first budget respects runtime
  exact frozen.trans (by gcongr)

end LaterHeadlineSymbolic

/-! ### The closed forms of `PqxdhDeploymentLaterHeadlineSymbolicLor` -/

section LaterHeadlineSymbolicLor
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
open PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `symbolic_lor_later_dct`: `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `functional`, `qInit`, `initBound`. -/
theorem symbolic_lor_later_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
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
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime) := by
  have frozen := PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later setup codec checks caps bounded
      shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second
      budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact frozen.trans (by gcongr)

/-- `symbolic_lor_later_bound_dct`: `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_later_bound_dct (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime) := by
  have frozen := PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound setup functional codec checks caps
      bounded shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first
      second budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit
      initBound post postRespects fallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P first budget respects runtime
  exact frozen.trans (by gcongr)

end LaterHeadlineSymbolicLor

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_app_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_app_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_app_beacon_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_app_beacon_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_kt_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_kt_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_kt_beacon_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.ce_kt_beacon_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_bound_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_bound_dct
