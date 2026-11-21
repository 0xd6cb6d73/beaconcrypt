-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGated

/-!
# The CE-12 headlines with `ctCollTerm`, closed (CE-12 P2b, design-v2 section 7.4)

P2 published the Beacon-side and mixed-side CE-12 headlines whose events can move the public designation between sessions that carry one ciphertext with the explicit public term `ctCollTerm` (`PqxdhDeploymentHeadlineCollision`), gated on design-v2's `ct_collision_game` (plan section 103, owner flag). `PqxdhDeploymentHeadlineCtColl.ct_coll_le` bounds that term by `ε_ctcoll = qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)` (`ctCollEps`). Each theorem below restates one of those headlines with `ctCollTerm` replaced by `ε_ctcoll`, by monotonicity of the bound in that term:

- `ce_or_s2b_sym_closed`, `ce_uks_sym_closed` (`PqxdhDeploymentHeadlineSymbolic`);
- `symbolic_lor_closed`, `symbolic_lor_bound_closed` (`PqxdhDeploymentHeadlineSymbolicLor`);
- `ce_or_injective_s2b_closed`, `ce_or_injective_s2b_full_closed` (`PqxdhDeploymentHeadlineInjective`);
- the billed forms of P2b step 1 (`PqxdhDeploymentHeadlineGated`), closed and with the bill of `pairAdversary` conjoined (`PqxdhDeploymentHeadlineBillsFull.PairBills`, from `PqxdhDeploymentHeadlineBills.pair_bills`): `ce_or_s2b_sym_closed_billed`, `ce_uks_sym_closed_billed`, `symbolic_lor_bound_closed_billed`, `ce_or_injective_s2b_closed_billed`, `ce_or_injective_s2b_full_closed_billed`.

The premises are the frozen theorems' own, which include those of `ct_coll_le` (`Phase1ReadBack`, `Phase2ReadBack`, `FunctionalDecapsulation`, the budget), except `symbolic_lor_closed`, which adds `FunctionalDecapsulation` (the premise of `pair_cp_le`, already a premise of every other CE-12 form with a KEM term). `ctGapTerm` stays explicit (F-ct2, D-ct deferred): the owner flag of plan section 103 on `ctGapTerm` stands, the one on `ctCollTerm` is closed by these forms. No assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

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
/-- `ce_or_s2b_sym` closed (`PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`): the same bound with the explicit ciphertext-collision term replaced by `qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (D-ct, deferred). -/
theorem ce_or_s2b_sym_closed (setup : Setup baseSpec KemSK)
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget :=
  (PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget respects
    runtime fallback a1Fallback signatureFallback).trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime))

open Classical in
/-- `ce_or_s2b_sym` closed and billed (`PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed` with `ctCollTerm` replaced by `ε_ctcoll`): the closed bound of `ce_or_s2b_sym_closed`, the bills of the frozen form's reductions, and the bill of `pairAdversary`, the reduction behind `ε_ctcoll` (`PairBills`, `PqxdhDeploymentHeadlineBills.pair_bills`). -/
theorem ce_or_s2b_sym_closed_billed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps :=
  ⟨(PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback).1.trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime)),
    (PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed setup functional codec checks route ensureInit phase1 phase2
      correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
      respects runtime fallback a1Fallback signatureFallback).2,
    PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded⟩

open Classical in
/-- `ce_uks_sym` closed (`PqxdhDeploymentHeadlineSymbolic.ce_uks_sym` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`): the same bound with the explicit ciphertext-collision term replaced by `qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (D-ct, deferred). -/
theorem ce_uks_sym_closed (setup : Setup baseSpec KemSK)
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
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget :=
  (PqxdhDeploymentHeadlineSymbolic.ce_uks_sym setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget respects
    runtime fallback a1Fallback signatureFallback).trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime))

open Classical in
/-- `ce_uks_sym` closed and billed (`PqxdhDeploymentHeadlineGated.ce_uks_sym_billed` with `ctCollTerm` replaced by `ε_ctcoll`): the closed bound of `ce_uks_sym_closed`, the bills of the frozen form's reductions, and the bill of `pairAdversary`, the reduction behind `ε_ctcoll` (`PairBills`, `PqxdhDeploymentHeadlineBills.pair_bills`). -/
theorem ce_uks_sym_closed_billed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps :=
  ⟨(PqxdhDeploymentHeadlineGated.ce_uks_sym_billed setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback).1.trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime)),
    (PqxdhDeploymentHeadlineGated.ce_uks_sym_billed setup functional codec checks route ensureInit phase1 phase2
      correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
      respects runtime fallback a1Fallback signatureFallback).2,
    PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded⟩

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
/-- `symbolic_lor` closed (`PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`): the same bound with the explicit ciphertext-collision term replaced by `qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (D-ct, deferred). It takes `FunctionalDecapsulation` in addition to the frozen theorem's premises: it is the premise of `pair_cp_le`, the KEM-level half of `ε_ctcoll`, and an existing premise of the KEM transfer, not a new assumption. -/
theorem symbolic_lor_closed (setup : Setup baseSpec KemSK)
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
    (signatureFallback : PqxdhJointIdentity.Forgery) :
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
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) :=
  (PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor setup codec checks caps bounded shortRejects route ensureInit
    phase1 phase2 frameBack writable law spread correct adapter bounds adversary budget respects runtime guess
    identityFallback ordinaryFallback a1Fallback signatureFallback).trans
    (mul_le_mul' le_rfl (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route
      ensureInit phase1 phase2 functional bounds .P adversary budget respects runtime)))

open Classical in
/-- `symbolic_lor_bound` closed (`PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`): the same bound with the explicit ciphertext-collision term replaced by `qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (D-ct, deferred). -/
theorem symbolic_lor_bound_closed (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) :=
  (PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound setup functional codec checks caps bounded shortRejects route
    ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct adapter bounds adversary budget
    respects runtime fallback guess identityFallback ordinaryFallback a1Fallback signatureFallback).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec
      checks route ensureInit phase1 phase2 functional bounds .P adversary budget respects runtime))))

open Classical in
/-- `symbolic_lor_bound` closed and billed (`PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed` with `ctCollTerm` replaced by `ε_ctcoll`): the closed bound of `symbolic_lor_bound_closed`, the bills of the frozen form's reductions, and the bill of `pairAdversary`, the reduction behind `ε_ctcoll` (`PairBills`, `PqxdhDeploymentHeadlineBills.pair_bills`). -/
theorem symbolic_lor_bound_closed_billed (setup : Setup baseSpec KemSK)
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
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P adversary
        budget runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps :=
  ⟨(PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed setup functional codec checks caps bounded shortRejects
    route ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct adapter bounds adversary
    budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback signatureFallback).1.trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec
      checks route ensureInit phase1 phase2 functional bounds .P adversary budget respects runtime)))),
    (PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed setup functional codec checks caps bounded shortRejects
      route ensureInit qInit initBound phase1 phase2 frameBack writable law spread correct adapter bounds adversary
      budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback signatureFallback).2,
    PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded⟩

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
/-- `ce_or_injective_s2b` closed (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`): the same bound with the explicit ciphertext-collision term replaced by `qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (D-ct, deferred). -/
theorem ce_or_injective_s2b_closed (setup : Setup baseSpec KemSK)
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
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget :=
  (PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback).trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime))

open Classical in
/-- `ce_or_injective_s2b` closed and billed (`PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed` with `ctCollTerm` replaced by `ε_ctcoll`): the closed bound of `ce_or_injective_s2b_closed`, the bills of the frozen form's reductions, and the bill of `pairAdversary`, the reduction behind `ε_ctcoll` (`PairBills`, `PqxdhDeploymentHeadlineBills.pair_bills`). -/
theorem ce_or_injective_s2b_closed_billed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps :=
  ⟨(PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback).1.trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime)),
    (PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed setup functional codec checks route ensureInit phase1
      phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary
      budget respects runtime fallback a1Fallback signatureFallback).2,
    PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded⟩

open Classical in
/-- `ce_or_injective_s2b_full` closed (`PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`): the same bound with the explicit ciphertext-collision term replaced by `qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (D-ct, deferred). -/
theorem ce_or_injective_s2b_full_closed (setup : Setup baseSpec KemSK)
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
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget :=
  (PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback).trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime))

open Classical in
/-- `ce_or_injective_s2b_full` closed and billed (`PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed` with `ctCollTerm` replaced by `ε_ctcoll`): the closed bound of `ce_or_injective_s2b_full_closed`, the bills of the frozen form's reductions, and the bill of `pairAdversary`, the reduction behind `ε_ctcoll` (`PairBills`, `PqxdhDeploymentHeadlineBills.pair_bills`). -/
theorem ce_or_injective_s2b_full_closed_billed (setup : Setup baseSpec KemSK)
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
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds mode adversary budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps :=
  ⟨(PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode adversary budget
    respects runtime fallback a1Fallback signatureFallback).1.trans
    (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route ensureInit phase1 phase2
      functional bounds mode adversary budget respects runtime)),
    (PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed setup functional codec checks route ensureInit
      phase1 phase2 correct caps bounded qInit initBound frameReadBack writable law spread adapter bounds mode
      adversary budget respects runtime fallback a1Fallback signatureFallback).2,
    PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded⟩

end Injective
end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.symbolic_lor_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.symbolic_lor_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed_billed
