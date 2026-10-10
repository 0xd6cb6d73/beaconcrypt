-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated

/-!
# CE-12 D-ct: closed forms of the P2b closed and gated headlines

The frozen P2b headlines of `PqxdhDeploymentHeadlineCtClosed` (the forms with `ctCollTerm` already closed by `ε_ctcoll`, and their billed forms) and of `PqxdhDeploymentHeadlineGated` (the billed forms of the symbolic, LoR and injective headlines) still carry the explicit public term `ctGapTerm`. Each theorem `T_dct` of this module is the frozen `T` with `ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime` replaced by `epsCt setup codec checks route ensureInit bounds mode adversary budget runtime` (`PqxdhDeploymentHeadlineDctEvent.epsCt`), proved as `T` followed by `PqxdhDeploymentHeadlineDctWorld.ctgap_term_le` under monotonicity (`gcongr`); every other term and every bills conjunct is unchanged (the `TargetBills` conjunct of a billed form is quantified over every event and claim, so it already bills the KEM and slot reductions of `epsCt`). The eleven `*_closed*_dct` forms carry neither `ctGapTerm` nor `ctCollTerm`: they are the fully closed CE-12 headlines. The Gated forms keep `ctCollTerm` explicit where their frozen sources do, and their `*_closed*_dct` siblings are the forms without it.

The premises are those of `T` plus those of `ctgap_term_le` that `T` lacks: `qInit` and `initBound` for `symbolic_lor_closed_dct`, none for the other seventeen. No frozen theorem changes.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### The closed forms of `PqxdhDeploymentHeadlineCtClosed` -/

section HeadlineCtClosed
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
open PqxdhDeploymentHeadlineSymbolicLor
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailure NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (protectedBinding)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt IdentityCollision)
open PqxdhDeploymentHeadlineSymbolic (SymHandle)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest admissibleTest)
open PqxdhDeploymentHeadlineEvents (LorElig)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineInjective
open PqxdhDeploymentHeadlineSymbolic (OriginFailureSym originSym)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim)
open PqxdhDeploymentHeadlineGap (a2pubTerm ctGapTerm chance_le_support chance_le_add_support)
open PqxdhRecordLiftIdeal (publicationTerm)
open PqxdhDeploymentHeadlineCtClosed
open PqxdhDeploymentHeadlineDctEvent (epsCt)

open Classical in
/-- `ce_or_s2b_sym_closed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_s2b_sym_closed_dct (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode
      adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

open Classical in
/-- `ce_or_s2b_sym_closed_billed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_s2b_sym_closed_billed_dct (setup : Setup baseSpec KemSK)
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed_billed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

open Classical in
/-- `ce_uks_sym_closed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_uks_sym_closed_dct (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode
      adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

open Classical in
/-- `ce_uks_sym_closed_billed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_uks_sym_closed_billed_dct (setup : Setup baseSpec KemSK)
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed_billed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

open Classical in
/-- `symbolic_lor_closed_dct`: `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). Added premises: `qInit`, `initBound`. -/
theorem symbolic_lor_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response)
    (checks : Checks)
    (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool)
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
    (guess : X → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery)
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.symbolic_lor_closed setup functional codec checks caps bounded
      shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds adversary
      budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact frozen.trans (by gcongr)

open Classical in
/-- `symbolic_lor_bound_closed_dct`: `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_bound_closed_dct (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed setup functional codec checks caps bounded
      shortRejects route ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct adapter bounds
      adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact frozen.trans (by gcongr)

open Classical in
/-- `symbolic_lor_bound_closed_billed_dct`: `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_bound_closed_billed_dct (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed_billed setup functional codec checks caps
      bounded shortRejects route ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

open Classical in
/-- `ce_or_injective_s2b_closed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_closed_dct (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

open Classical in
/-- `ce_or_injective_s2b_closed_billed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_closed_billed_dct (setup : Setup baseSpec KemSK)
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
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed_billed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

open Classical in
/-- `ce_or_injective_s2b_full_closed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_full_closed_dct (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact frozen.trans (by gcongr)

open Classical in
/-- `ce_or_injective_s2b_full_closed_billed_dct`: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_full_closed_billed_dct (setup : Setup baseSpec KemSK)
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
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  have frozen := PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed_billed setup functional codec checks
      route ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter
      bounds mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

end HeadlineCtClosed

/-! ### The closed forms of `PqxdhDeploymentHeadlineGated` -/

section HeadlineGated
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (Anomaly)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineAnomaly (beta ptc)
open PqxdhDeploymentHeadlineApp
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss recLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineOrigin
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth publicationTerm)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents (Direction originEvent orClaim)
open PqxdhDeploymentHeadlineUks
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealAuth bindingTerm)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineEvents (uksReceiverEvent uksReceiverClaim uksSenderEvent uksSenderClaim)
open PqxdhDeploymentHeadlineLor
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealTrace (IdealSlots peerOf)
open PqxdhDeploymentTranscript (SameView designateIn)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View PublicHiding publicHiding firstTest AdmittedTest testBit)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents
open PqxdhRecordLiftIdeal (ctxView idealRecords)
open PqxdhDeploymentHeadlineChain (EnvG)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineSymbolic
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
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineSymbolicLor
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailure NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (protectedBinding)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt IdentityCollision)
open PqxdhDeploymentHeadlineSymbolic (SymHandle)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest admissibleTest)
open PqxdhDeploymentHeadlineEvents (LorElig)
open PqxdhDeploymentHeadlineEvents (LorElig LorWin lorEligEvent lorWinEvent lorClaim)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support
  chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm injTerm)
open PqxdhDeploymentHeadlineInjective
open PqxdhDeploymentHeadlineSymbolic (OriginFailureSym originSym)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim)
open PqxdhDeploymentHeadlineGap (a2pubTerm ctGapTerm chance_le_support chance_le_add_support)
open PqxdhRecordLiftIdeal (publicationTerm)
open PqxdhDeploymentHeadlineGated
open PqxdhDeploymentHeadlineDctEvent (epsCt)

open Classical in
/-- `ce_or_s2b_sym_billed_dct`: `PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_s2b_sym_billed_dct (setup : Setup baseSpec KemSK)
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback := by
  have frozen := PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode
      adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

open Classical in
/-- `ce_uks_sym_billed_dct`: `PqxdhDeploymentHeadlineGated.ce_uks_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_uks_sym_billed_dct (setup : Setup baseSpec KemSK)
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback := by
  have frozen := PqxdhDeploymentHeadlineGated.ce_uks_sym_billed setup functional codec checks route ensureInit phase1
      phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary
      budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

open Classical in
/-- `ce_app_beacon_sym_billed_dct`: `PqxdhDeploymentHeadlineGated.ce_app_beacon_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_beacon_sym_billed_dct (setup : Setup baseSpec KemSK)
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
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        epsCt setup codec checks route ensureInit bounds .P adversary budget runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback := by
  have frozen := PqxdhDeploymentHeadlineGated.ce_app_beacon_sym_billed setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds adversary
      budget respects runtime fallback appClaim a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2⟩

open Classical in
/-- `ce_app_sym_billed_dct`: `PqxdhDeploymentHeadlineGated.ce_app_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_app_sym_billed_dct (setup : Setup baseSpec KemSK)
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
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup codec checks route ensureInit bounds .P adversary budget runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback := by
  have frozen := PqxdhDeploymentHeadlineGated.ce_app_sym_billed setup functional codec checks route ensureInit phase1
      phase2 correct caps bounded qInit initBound shortRejects frameReadBack writable law spread adapter bounds
      adversary budget respects runtime fallback appClaim identityFallback ordinaryFallback a1Fallback
      signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2.1, frozen.2.2.2⟩

open Classical in
/-- `symbolic_lor_bound_billed_dct`: `PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem symbolic_lor_bound_billed_dct (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P adversary runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  have frozen := PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed setup functional codec checks caps bounded
      shortRejects route ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct adapter bounds
      adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameBack correct caps bounded qInit initBound bounds .P adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2.1, frozen.2.2.2.1, frozen.2.2.2.2⟩

open Classical in
/-- `ce_or_injective_s2b_billed_dct`: `PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_billed_dct (setup : Setup baseSpec KemSK)
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
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  have frozen := PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2.1, frozen.2.2.2⟩

open Classical in
/-- `ce_or_injective_s2b_full_billed_dct`: `PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`). -/
theorem ce_or_injective_s2b_full_billed_dct (setup : Setup baseSpec KemSK)
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
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  have frozen := PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds
      mode adversary budget respects runtime fallback a1Fallback signatureFallback
  have closed := PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup codec checks route ensureInit functional phase1
      phase2 frameReadBack correct caps bounded qInit initBound bounds mode adversary budget respects runtime
  exact ⟨frozen.1.trans (by gcongr), frozen.2.1, frozen.2.2.1, frozen.2.2.2⟩

end HeadlineGated

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_app_beacon_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_app_beacon_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_app_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_app_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_billed_dct
