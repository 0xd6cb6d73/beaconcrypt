-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective

/-!
# CE-12 D-ct: closed forms of the gap, symbolic, LoR and injective headlines

The frozen CE-12 headlines of `PqxdhDeploymentHeadlineGap`, `PqxdhDeploymentHeadlineSymbolic`, `PqxdhDeploymentHeadlineSymbolicLor` and `PqxdhDeploymentHeadlineInjective` bound their events with the explicit public term `ctGapTerm`, the probability of the ciphertext gap. Each theorem `T_dct` of this module is the frozen `T` with `ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime` replaced by `epsCt setup codec checks route ensureInit bounds mode adversary budget runtime` (`PqxdhDeploymentHeadlineDctEvent.epsCt`: over every target, the KEM and slot losses of the decision of `(ctGapNamed, ctClaim)` and `ctStat = r1Cap/2^256 + C(ctxCap, 2)/2^512`). The proof is `T` followed by `PqxdhDeploymentHeadlineDctWorld.ctgap_term_le` under monotonicity (`gcongr`). Every other term, including `ctCollTerm` where the frozen form carries it, and every other conjunct (the bills of `ce_a1_linked`) are unchanged, and no frozen theorem changes.

The premises are those of `T` plus those of `ctgap_term_le` that `T` lacks: `FunctionalDecapsulation`, `qInit` and `initBound` for `ce_a1_linked_dct`, `sym_gap_dct` and `symbolic_lor_dct`; `qInit` and `initBound` for `ce_kt_sym_dct` and `ce_kt_beacon_sym_dct`; none for the other seven.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### The closed forms of `PqxdhDeploymentHeadlineGap` -/

section HeadlineGap
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf regOfEntry summarizeReg stepReg accepted acceptedFrom publishedKeys
  keysOfBundle bundleOfReg protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (OwnerForgery OwnerEvent ownerIdentities publishedTuple candidateTuple)
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)
open PqxdhDeploymentHeadlineGap
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `ce_a1_linked_dct`: `PqxdhDeploymentHeadlineGap.ce_a1_linked` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `functional`, `qInit`, `initBound`. -/
theorem ce_a1_linked_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[beaconGap setup codec budget <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget fallback signatureFallback) +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
      (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
      (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget)
      (PqxdhDeploymentServerAuthBills.totalCap caps bounds budget) budget.finish fallback signatureFallback := by
  have frozen := PqxdhDeploymentHeadlineGap.ce_a1_linked setup codec checks caps bounded route ensureInit phase1
      phase2 frameBack writable law spread correct adapter bounds mode adversary budget respects runtime fallback
      signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2⟩

/-- `sym_gap_dct`: `PqxdhDeploymentHeadlineGap.sym_gap` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `functional`, `qInit`, `initBound`. -/
theorem sym_gap_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[(fun outcome => serverGap setup codec budget outcome || beaconGap setup codec budget outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      a2pubTerm setup codec checks route ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget fallback signatureFallback) +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime := by
  have frozen := PqxdhDeploymentHeadlineGap.sym_gap setup codec checks caps bounded shortRejects route ensureInit
      phase1 phase2 frameBack writable law spread correct adapter bounds mode adversary budget respects runtime
      identityFallback ordinaryFallback fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

end HeadlineGap

/-! ### The closed forms of `PqxdhDeploymentHeadlineSymbolic` -/

section HeadlineSymbolic
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
open PqxdhDeploymentHeadlineSymbolic
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `ce_or_s2b_sym_dct`: `PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_s2b_sym_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[originSym setup codec route .s2b <$>
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  have frozen := PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym setup functional codec checks route ensureInit phase1
      phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary
      budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_uks_sym_dct`: `PqxdhDeploymentHeadlineSymbolic.ce_uks_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_uks_sym_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[uksSym setup codec route <$>
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  have frozen := PqxdhDeploymentHeadlineSymbolic.ce_uks_sym setup functional codec checks route ensureInit phase1
      phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary
      budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_app_sym_dct`: `PqxdhDeploymentHeadlineSymbolic.ce_app_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_sym_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[appSym setup codec appClaim <$>
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
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup codec checks route ensureInit bounds .P adversary budget runtime) := by
  have frozen := PqxdhDeploymentHeadlineSymbolic.ce_app_sym setup functional codec checks route ensureInit phase1
      phase2 correct caps bounded qInit initBound shortRejects frameReadBack writable law spread adapter bounds
      adversary budget respects runtime fallback appClaim identityFallback ordinaryFallback a1Fallback
      signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_kt_sym_dct`: `PqxdhDeploymentHeadlineSymbolic.ce_kt_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `qInit`, `initBound`. -/
theorem ce_kt_sym_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[ktSym setup codec event claim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup codec checks route ensureInit bounds mode adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback
            signatureFallback) +
        epsCt setup codec checks route ensureInit bounds mode adversary budget runtime) := by
  have frozen := PqxdhDeploymentHeadlineSymbolic.ce_kt_sym setup functional codec checks route ensureInit phase1
      phase2 correct caps bounded shortRejects frameReadBack writable law spread adapter bounds mode adversary budget
      respects event claim runtime identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_app_beacon_sym_dct`: `PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_beacon_sym_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[appOwnerSym setup appClaim <$>
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
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P adversary budget runtime) := by
  have frozen := PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds adversary
      budget respects runtime fallback appClaim a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_kt_beacon_sym_dct`: `PqxdhDeploymentHeadlineSymbolic.ce_kt_beacon_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `qInit`, `initBound`. -/
theorem ce_kt_beacon_sym_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[ktOwnerSym setup event claim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback)
          +
        epsCt setup codec checks route ensureInit bounds mode adversary budget runtime) := by
  have frozen := PqxdhDeploymentHeadlineSymbolic.ce_kt_beacon_sym setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded frameReadBack writable law spread adapter bounds mode adversary budget
      respects event claim runtime a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

end HeadlineSymbolic

/-! ### The closed forms of `PqxdhDeploymentHeadlineSymbolicLor` -/

section HeadlineSymbolicLor
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
open PqxdhDeploymentHeadlineSymbolicLor
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `symbolic_lor_dct`: `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `functional`, `qInit`, `initBound`. -/
theorem symbolic_lor_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    ENNReal.ofReal |((𝒟[lorWinSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal) -
      ((𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter)
          outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget
          nbfFilter) outcome) <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup codec checks route ensureInit bounds .P adversary budget runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime) := by
  have frozen := PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor setup codec checks caps bounded shortRejects route
      ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds adversary budget respects runtime
      guess identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact frozen.trans (by gcongr)

/-- `symbolic_lor_bound_dct`: `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_bound_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[lorWinSym setup codec guess <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[lorEligSym setup codec <$>
          (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
            {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
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
            recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime
                fallback
              caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup codec checks route ensureInit bounds .P adversary budget runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime) := by
  have frozen := PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound setup functional codec checks caps bounded
      shortRejects route ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct adapter bounds
      adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact frozen.trans (by gcongr)

end HeadlineSymbolicLor

/-! ### The closed forms of `PqxdhDeploymentHeadlineInjective` -/

section HeadlineInjective
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
open PqxdhDeploymentHeadlineInjective
open PqxdhDeploymentHeadlineDctEvent (epsCt)

/-- `ce_or_injective_s2b_dct`: `PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[injectiveS2b setup codec route <$>
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
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  have frozen := PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode
      adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

/-- `ce_or_injective_s2b_full_dct`: `PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_full_dct (setup : Setup baseSpec KemSK)
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
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[injectiveS2bFull setup codec route <$>
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
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  have frozen := PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

end HeadlineInjective

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_a1_linked_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_a1_linked_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.sym_gap_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.sym_gap_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_or_s2b_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_or_s2b_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_uks_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_uks_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_app_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_app_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_kt_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_kt_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_app_beacon_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_app_beacon_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_kt_beacon_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_kt_beacon_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.symbolic_lor_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.symbolic_lor_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.symbolic_lor_bound_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.symbolic_lor_bound_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_full_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_full_dct
