-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosed
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedP2b
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLater
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctClosedLaterP4
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld

/-!
# Production composition of items 3 and 7: the CE-12 D-ct closed headlines on the production source games

Follow-up to `PqxdhDeploymentProductionHeadlines` (which stays as published): every theorem of this module is the production form of a published CE-12 D-ct theorem of item 3 (section "CE-12 D-ct: ..." of `doc/impl/common-deployment-experiment.md`) and keeps the frozen theorem's name. The D-ct theorems close the explicit ciphertext-gap term `ctGapTerm` of the gap, symbolic, symbolic-LOR, injective, billed and closed headlines by `PqxdhDeploymentHeadlineDctEvent.epsCt` (over every target, the KEM and slot losses of the decision of `(ctGapNamed, ctClaim)` and `ctStat = r1Cap/2^256 + C(ctxCap, 2)/2^512`):

- the twelve `_dct` forms of `PqxdhDeploymentHeadlineDctClosed`, the eighteen of `PqxdhDeploymentHeadlineDctClosedP2b` and the six later forms of `PqxdhDeploymentHeadlineDctClosedLater` (LQ-F game, `epsCt` at the run-phase adversary `first`);
- the six later P4 `_dct` forms of `PqxdhDeploymentHeadlineDctClosedLaterP4` and its four siblings `*_billed_dct_full`, which add `TargetBills` at mode `.P` and adversary `first` (the bills of `epsCt`'s reductions);
- the closure lemmas `ctgap_term_le` (`ctGapTerm ≤ epsCt`) and `ctgap_term_billed` (with `TargetBills`) of `PqxdhDeploymentHeadlineDctWorld`, whose left side `ctGapTerm` is unfolded to its definition and moved: the probability of the public ciphertext gap on the classical production source game is at most `epsCt` at the production codec and route.

Each production form is the frozen statement instantiated at the production codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and route `route′ = RawCtxFrameDecoding.sender reader.model` of item 7, with every probability of the CE experiment `PqxdhDeploymentSecrecy.game … 0 …` (LQ-F experiment `PqxdhDeploymentLaterServerGame.game … 0 … first second`) replaced by the probability of the same event, read back through `PqxdhBoundaryDeployment.unwrap` (`PqxdhBoundaryDeploymentLater.unwrap`), on the PB-D production source game `PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 …` (`PqxdhBoundaryDeploymentLater.laterSourceGame … first second`), through `PqxdhDeploymentProductionTransfer.chance` (`chance_later`). The rest of the conclusion is the frozen text at codec′ and route′: `epsCt` and the other terms (losses, `a1Term`, `a2pubTerm`, `injTerm`, `ctCollTerm` where the frozen form keeps it, `ctCollEps`, the anomaly term, and in the four symbolic key-transfer forms `ce_kt_sym_dct`, `ce_kt_beacon_sym_dct`, `ce_kt_later_sym_dct` and `ce_kt_beacon_later_sym_dct` the per-target probabilities of the event in CE's ideal key-transfer game (`PqxdhDeploymentIdealSteps.idealGame`, `PqxdhDeploymentIdealLaterGame.idealLaterGame` in the later forms), which their bounds keep as the frozen forms do) are CE-model quantities at the production instance, and the bills are the frozen ones. In the later forms `epsCt`, like the other classical run-phase terms, is taken at `first`. Premises: the frozen ones at codec′ and route′, except that `Phase1ReadBack` and `Phase2ReadBack` are stated at `codec` and transported by `PqxdhBoundaryDeploymentStep.phase1_withReader` and `phase2_withReader` (`Iff.rfl`); `FrameReadBack` and `ReadWritable` are carried at codec′ exactly where the frozen theorem takes them. No D-ct theorem takes `DecoderAgreement`. The later mode stays confidentiality only. Each proof is `simp only` with the transfer lemma followed by the frozen theorem. No assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct

variable {ι KemSK Reader Response Message Root A X Out : Type} {baseSpec : OracleSpec ι}

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_a1_linked_dct` (frozen: `PqxdhDeploymentHeadlineGap.ce_a1_linked` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_a1_linked_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[(beaconGap setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget fallback signatureFallback) +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
      (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
      (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget)
      (PqxdhDeploymentServerAuthBills.totalCap caps bounds budget) budget.finish fallback signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_a1_linked_dct setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps bounded (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime fallback signatureFallback functional qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.sym_gap_dct` (frozen: `PqxdhDeploymentHeadlineGap.sym_gap` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem sym_gap_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[((fun outcome => serverGap setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget outcome || beaconGap
      setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback +
      ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget fallback signatureFallback) +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.sym_gap_dct setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      caps bounded shortRejects (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime identityFallback ordinaryFallback fallback signatureFallback
      functional qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_or_s2b_sym_dct` (frozen: `PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_or_s2b_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_uks_sym_dct` (frozen: `PqxdhDeploymentHeadlineSymbolic.ce_uks_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_uks_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_app_sym_dct` (frozen: `PqxdhDeploymentHeadlineSymbolic.ce_app_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    𝒟[(appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim ∘ PqxdhBoundaryDeployment.unwrap) <$>
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
                budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_app_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim
      identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_kt_sym_dct` (frozen: `PqxdhDeploymentHeadlineSymbolic.ce_kt_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (runtime : A) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[(ktSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) event claim ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
              reader) setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback
            signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_kt_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded shortRejects
      frameReadBack writable law spread adapter bounds mode adversary budget respects event claim runtime
      identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_app_beacon_sym_dct` (frozen: `PqxdhDeploymentHeadlineSymbolic.ce_app_beacon_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    𝒟[(appOwnerSym setup appClaim ∘ PqxdhBoundaryDeployment.unwrap) <$>
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
                budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_app_beacon_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_kt_beacon_sym_dct` (frozen: `PqxdhDeploymentHeadlineSymbolic.ce_kt_beacon_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_beacon_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (runtime : A) (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[(ktOwnerSym setup event claim ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec
              reader) setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_kt_beacon_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded frameReadBack
      writable law spread adapter bounds mode adversary budget respects event claim runtime a1Fallback signatureFallback
      qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.symbolic_lor_dct` (frozen: `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
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
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.symbolic_lor_dct setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps bounded shortRejects (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback functional qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.symbolic_lor_bound_dct` (frozen: `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor_bound` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
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
                runtime
                fallback
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
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.symbolic_lor_bound_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_dct` (frozen: `PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosed
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_full_dct` (frozen: `PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosed.ce_or_injective_s2b_full_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_billed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_or_s2b_sym_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym_closed_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_closed_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_billed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_uks_sym_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym_closed_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) ∧
      (PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_closed_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_closed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
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
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
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
                runtime
                fallback
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
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_billed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.symbolic_lor_bound_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound_closed_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
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
                runtime
                fallback
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
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime +
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
  exact PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_closed_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_billed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_closed_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
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
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_closed_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_billed_dct` (frozen: `PqxdhDeploymentHeadlineCtClosed.ce_or_injective_s2b_full_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full_closed_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
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
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_closed_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_billed_dct` (frozen: `PqxdhDeploymentHeadlineGated.ce_or_s2b_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_s2b_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_s2b_sym_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_billed_dct` (frozen: `PqxdhDeploymentHeadlineGated.ce_uks_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_uks_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary budget a1Fallback signatureFallback)
          +
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
      ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary runtime) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode
        adversary budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds mode adversary budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_uks_sym_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_app_beacon_sym_billed_dct` (frozen: `PqxdhDeploymentHeadlineGated.ce_app_beacon_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
                budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime)) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P adversary
        budget runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P adversary budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_app_beacon_sym_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_app_sym_billed_dct` (frozen: `PqxdhDeploymentHeadlineGated.ce_app_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
                budget
                appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime)) ∧
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
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_app_sym_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds adversary budget respects runtime fallback appClaim
      identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_billed_dct` (frozen: `PqxdhDeploymentHeadlineGated.symbolic_lor_bound_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_bound_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
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
                runtime
                fallback
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
          (RawCtxFrameDecoding.sender reader.model) bounds .P adversary budget a1Fallback signatureFallback)
            +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P adversary budget runtime +
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
  exact PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_bound_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit qInit initBound
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds adversary budget respects runtime fallback guess identityFallback ordinaryFallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_billed_dct` (frozen: `PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
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
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedP2b
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
/-- Production form of `PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_billed_dct` (frozen: `PqxdhDeploymentHeadlineGated.ce_or_injective_s2b_full_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_or_injective_s2b_full_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime +
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
  exact PqxdhDeploymentHeadlineDctClosedP2b.ce_or_injective_s2b_full_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds mode adversary budget respects runtime fallback a1Fallback
      signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedLater
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLater.ce_app_later_sym_dct` (frozen: `PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLater.ce_app_later_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds first second budget respects post postRespects
      runtime fallback appClaim identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedLater
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLater.ce_app_beacon_later_sym_dct` (frozen: `PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_later_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[((fun outcome => appOwnerSym setup appClaim (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLater.ce_app_beacon_later_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds first second budget respects post postRespects runtime fallback
      appClaim a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedLater
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLater.ce_kt_later_sym_dct` (frozen: `PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_later_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
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
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[((fun outcome => ktSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) event claim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds mode first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLater.ce_kt_later_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded shortRejects
      frameReadBack writable law spread adapter bounds mode first second budget respects post postRespects event claim
      runtime identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosedLater
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLater.ce_kt_beacon_later_sym_dct` (frozen: `PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_kt_beacon_later_sym_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    𝒟[((fun outcome => ktOwnerSym setup event claim (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
          event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              (RawCtxFrameDecoding.sender reader.model) checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds mode first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode first budget runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLater.ce_kt_beacon_later_sym_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded frameReadBack
      writable law spread adapter bounds mode first second budget respects post postRespects event claim runtime
      a1Fallback signatureFallback qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosedLater
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_dct` (frozen: `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_dct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal) -
      ((𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            guess nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_dct setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback functional qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosedLater
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_bound_dct` (frozen: `PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLater.symbolic_lor_later_bound_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct` (frozen: `PqxdhDeploymentLaterHeadlineGated.ce_app_later_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds first second budget respects post postRespects
      runtime fallback appClaim identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct_full` (frozen: `ce_app_later_sym_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_later_sym_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ((𝒟[((fun outcome => appSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) appClaim
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_later_sym_billed_dct_full setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      shortRejects frameReadBack writable law spread adapter bounds first second budget respects post postRespects
      runtime fallback appClaim identityFallback ordinaryFallback a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct` (frozen: `PqxdhDeploymentLaterHeadlineGated.ce_app_beacon_later_sym_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_later_sym_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => appOwnerSym setup appClaim (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds first second budget respects post postRespects runtime fallback
      appClaim a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct_full` (frozen: `ce_app_beacon_later_sym_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_app_beacon_later_sym_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ((𝒟[((fun outcome => appOwnerSym setup appClaim (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (appEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
              appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
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
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.ce_app_beacon_later_sym_billed_dct_full setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) correct caps bounded qInit initBound
      frameReadBack writable law spread adapter bounds first second budget respects post postRespects runtime fallback
      appClaim a1Fallback signatureFallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct` (frozen: `PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct_full` (frozen: `symbolic_lor_later_bound_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ((ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + ctCollTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first runtime)) ∧
      LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first second
        budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_billed_dct_full setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_closed_dct` (frozen: `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal) -
      ((𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId budget
            guess nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
            budget nbfFilter) outcome) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_dct` (frozen: `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_closed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct` (frozen: `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed` with the explicit ciphertext-gap term `ctGapTerm` replaced by `epsCt` (`PqxdhDeploymentHeadlineDctWorld.ctgap_term_le`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_closed_billed_dct (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentLaterHeadlineGated.LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P
        first second budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentHeadlineDctClosedLaterP4
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

/-- Production form of `PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct_full` (frozen: `symbolic_lor_later_bound_closed_billed_dct` together with `PqxdhDeploymentHeadlineBillsFull.TargetBills` at mode `.P` and adversary `first`, the bills of the attackers behind the KEM and slot reductions of its `epsCt` term (the second conjunct of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed`, proved by `PqxdhDeploymentHeadlineBillsFull.target_bills`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the LQ-F source game `PqxdhBoundaryDeploymentLater.laterSourceGame` (`PqxdhDeploymentProductionTransfer.chance_later`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem symbolic_lor_later_bound_closed_billed_dct_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
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
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ((ENNReal.ofReal |((𝒟[((fun outcome => lorWinSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader) guess
      (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[((fun outcome => lorEligSym setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (asClassical outcome)) ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds .P first
          second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim (g.1,
                g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget
            post (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
              budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post (g.1, g.2.castSucc)
              runtime
            fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
              (lorWinEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
            (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
              checks (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader)
                setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
              (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first second budget post
                (g.1, g.2.castSucc)
                runtime
              fallback caps qInit (slotted setup (PqxdhBoundaryRecordPrelude.withReader codec reader) budget
                (lorEligEvent setup.source.crypto (PqxdhBoundaryRecordPrelude.withReader codec reader) setup.serverKeyId
                  budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
            (RawCtxFrameDecoding.sender reader.model) checks ensureInit bounds .P first budget (g.1, g.2.castSucc)
              runtime)) +
      2⁻¹ * (a2pubTerm setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
          (RawCtxFrameDecoding.sender reader.model) bounds .P first budget a1Fallback signatureFallback) +
        epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds .P first budget runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentLaterHeadlineGated.LaterTargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P
        first second budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps) ∧
      PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds .P first budget
        runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance_later]
  exact PqxdhDeploymentHeadlineDctClosedLaterP4.symbolic_lor_later_bound_closed_billed_dct_full setup functional
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded shortRejects
      (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds first second budget respects runtime guess identityFallback ordinaryFallback a1Fallback
      signatureFallback qInit initBound post postRespects fallback

end

section
open PqxdhDeploymentHeadlineDctWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealProvenance (BuiltIn)
open PqxdhServerAuthNegativeControl (Phase1ReadBack Phase2ReadBack FrameReadBack)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineDctEvent (LinkedGap ctSession ctClaim ctGapNamed ctStat epsCt)
open PqxdhDeploymentHeadlineDctCommit (CommitAt)
open PqxdhDeploymentHeadlineDctTable (KeyHit)
open PqxdhDeploymentHeadlineDctHash (CtxColl)

/-- Production form of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_le` (frozen: the explicit ciphertext-gap term of the frozen headlines is at most `epsCt` (`ctgap_term_world`, then `ctgap_world` at each target)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The left side `ctGapTerm` of the frozen statement is unfolded to its definition (the probability of `ctGapEvent` on the CE experiment) before it is moved. -/
theorem ctgap_term_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (phase1 : Phase1ReadBack codec)
    (phase2 : Phase2ReadBack codec) (frameBack : FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) :
    𝒟[((fun outcome => PqxdhDeploymentKemTransfer.happens (PqxdhDeploymentHeadlineGap.ctGapEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctWorld.ctgap_term_le setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit functional
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack correct caps bounded qInit
      initBound bounds mode adversary budget respects runtime

end

section
open PqxdhDeploymentHeadlineDctWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealProvenance (BuiltIn)
open PqxdhServerAuthNegativeControl (Phase1ReadBack Phase2ReadBack FrameReadBack)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineDctEvent (LinkedGap ctSession ctClaim ctGapNamed ctStat epsCt)
open PqxdhDeploymentHeadlineDctCommit (CommitAt)
open PqxdhDeploymentHeadlineDctTable (KeyHit)
open PqxdhDeploymentHeadlineDctHash (CtxColl)

/-- Production form of `PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed` (frozen: `ctgap_term_le` with the bills of every reduction of `epsCt` (`PqxdhDeploymentHeadlineBillsFull.target_bills`, whose KEM and slot fields are quantified over every event and claim, so they bill the KEM and slot losses at `(ctGapNamed, ctClaim)`)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`); everything else in the conclusion (the closing term `epsCt`, every other term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The left side `ctGapTerm` of the frozen statement is unfolded to its definition (the probability of `ctGapEvent` on the CE experiment) before it is moved. -/
theorem ctgap_term_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (phase1 : Phase1ReadBack codec)
    (phase2 : Phase2ReadBack codec) (frameBack : FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[((fun outcome => PqxdhDeploymentKemTransfer.happens (PqxdhDeploymentHeadlineGap.ctGapEvent setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader)) outcome) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      epsCt setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
        ensureInit bounds mode adversary budget runtime ∧
    PqxdhDeploymentHeadlineBillsFull.TargetBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) caps ensureInit qInit bounds mode adversary
      budget runtime := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks (RawCtxFrameDecoding.sender reader.model) ensureInit functional
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack correct caps bounded qInit
      initBound bounds mode adversary budget respects runtime fallback

end

end BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_a1_linked_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_a1_linked_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.sym_gap_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.sym_gap_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_beacon_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_beacon_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_s2b_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_uks_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_bound_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_or_injective_s2b_full_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_beacon_later_sym_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_kt_beacon_later_sym_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_later_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_later_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_later_sym_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_later_sym_billed_dct_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_later_sym_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_later_sym_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_later_sym_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ce_app_beacon_later_sym_billed_dct_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_billed_dct_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_closed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_closed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_closed_billed_dct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_closed_billed_dct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_closed_billed_dct_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.symbolic_lor_later_bound_closed_billed_dct_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ctgap_term_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ctgap_term_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ctgap_term_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionHeadlinesDct.ctgap_term_billed
