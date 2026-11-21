-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineGated
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl

/-!
# The later-quantum CE-12 forms with `ctCollTerm`, closed (CE-12 P4 step 1, P3b; design-v2 section 7.4)

CE-12 P3's later symbolic LOR forms carry CE-12 P2's explicit public term `ctCollTerm` of the classical experiment of the run-phase adversary `first` (the probability that two distinct sessions carry one ciphertext to the PQ key of an owner's first published bundle, moved from the LQ-F game to the classical experiment of `first` by `PqxdhDeploymentLaterHeadlineSymbolicLor.collisions_later`). CE-12 P2b's `PqxdhDeploymentHeadlineCtColl.ct_coll_le` bounds that term, for every budget-respecting run-phase adversary, by `ε_ctcoll = qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)` (`ctCollEps`). Each theorem below restates one of the P3 forms with `ctCollTerm` (at `first`) replaced by `ε_ctcoll`, by monotonicity of the bound in that term, and is otherwise word for word the P3 statement:

- `symbolic_lor_later_closed` (`PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later`): `|adv_sym − adv_CE| ≤ ½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ε_ctcoll)`;
- `symbolic_lor_later_bound_closed` (`symbolic_lor_later_bound`): CE-LOR-L's bound at the NoBundleFailure filter plus the same half;
- `symbolic_lor_later_bound_closed_billed` (`PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed`): the closed bound with the bills of the P3 form's reductions and the bill of `pairAdversary` (`PqxdhDeploymentHeadlineBillsFull.PairBills`, from `PqxdhDeploymentHeadlineBills.pair_bills`).

No other P3 form carries `ctCollTerm`: the later APP and KT symbolic forms carry `ctGapTerm` only, and the Server-side LOR forms carry neither. The premises are the P3 theorems' own, which include those of `ct_coll_le` (`Phase1ReadBack`, `Phase2ReadBack`, the run budget of `first`, and `FunctionalDecapsulation` for the `_bound` forms), except `symbolic_lor_later_closed`, which adds `FunctionalDecapsulation` (the premise of `pair_cp_le`, already a premise of every later form with a KEM term). `ctGapTerm` stays explicit (F-ct2, D-ct deferred): P2's owner flag on `ctGapTerm` stands, the one on `ctCollTerm` is closed for the later forms by these theorems. The term is bounded on the classical experiment of `first`, never on the later compiled program. No assumption or contract is added. Later mode claims confidentiality only: no origin, binding or authentication statement.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

section SymbolicLor
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

/-- `symbolic_lor_later` closed (`PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le` at the run-phase adversary `first`): the same bound with the explicit ciphertext-collision term of the classical experiment of `first` replaced by `qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (F-ct2, D-ct deferred). It takes `FunctionalDecapsulation` in addition to the P3 theorem's premises: it is the premise of `pair_cp_le`, the KEM-level half of `ε_ctcoll`, and an existing premise of the KEM transfer, not a new assumption. -/
theorem symbolic_lor_later_closed (setup : Setup baseSpec KemSK)
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
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal) -
      ((𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) :=
  (PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later setup codec checks caps bounded shortRejects route
    ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second budget respects runtime
    guess identityFallback ordinaryFallback a1Fallback signatureFallback).trans
    (mul_le_mul' le_rfl (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec checks route
      ensureInit phase1 phase2 functional bounds .P first budget respects runtime)))

/-- `symbolic_lor_later_bound` closed (`PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound` with `ctCollTerm` replaced by `ε_ctcoll`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le` at the run-phase adversary `first`): the same bound, CE-LOR-L's bound at the NoBundleFailure filter plus `½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ε_ctcoll)`, with `ε_ctcoll = qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ctGapTerm` stays explicit (F-ct2, D-ct deferred). -/
theorem symbolic_lor_later_bound_closed (setup : Setup baseSpec KemSK)
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
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
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
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget) :=
  (PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound setup functional codec checks caps bounded
    shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second
    budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound post
    postRespects fallback).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec
      checks route ensureInit phase1 phase2 functional bounds .P first budget respects runtime))))

/-- `symbolic_lor_later_bound` closed and billed (`PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed` with `ctCollTerm` replaced by `ε_ctcoll`): the closed bound of `symbolic_lor_later_bound_closed`, the bills of the P3 form's reductions (`LaterTargetBills`, `A2Bills`, `A1Bills`, `InjBills`), and the bill of `pairAdversary`, the reduction behind `ε_ctcoll` (`PairBills`, `PqxdhDeploymentHeadlineBills.pair_bills`). -/
theorem symbolic_lor_later_bound_closed_billed (setup : Setup baseSpec KemSK)
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
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    (ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
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
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime +
        injTerm setup budget + PqxdhDeploymentHeadlineCtColl.ctCollEps setup budget)) ∧
      (PqxdhDeploymentLaterHeadlineGated.LaterTargetBills setup codec checks route caps ensureInit qInit bounds .P
        first second budget post runtime ∧
      PqxdhDeploymentHeadlineBillsFull.A2Bills setup codec checks route caps ensureInit qInit bounds .P first budget
        runtime identityFallback ordinaryFallback ∧
      PqxdhDeploymentHeadlineBillsFull.A1Bills setup codec checks route caps bounds .P first budget a1Fallback
        signatureFallback ∧
      PqxdhDeploymentHeadlineBillsFull.InjBills setup budget) ∧
      PqxdhDeploymentHeadlineBillsFull.PairBills setup caps :=
  ⟨(PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed setup functional codec checks caps bounded
    shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second
    budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound post
    postRespects fallback).1.trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl (PqxdhDeploymentHeadlineCtColl.ct_coll_le setup codec
      checks route ensureInit phase1 phase2 functional bounds .P first budget respects runtime)))),
   (PqxdhDeploymentLaterHeadlineGated.symbolic_lor_later_bound_billed setup functional codec checks caps bounded
     shortRejects route ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second
     budget respects runtime guess identityFallback ordinaryFallback a1Fallback signatureFallback qInit initBound post
     postRespects fallback).2,
   PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded⟩

end SymbolicLor

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_bound_closed_billed
