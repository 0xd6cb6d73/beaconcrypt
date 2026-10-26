-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement
import BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer

/-!
# Production forms of the ten-field session agreement (O21, part 4)

`ce_a1_agreement` and `ce_a1_agreement_billed` of `PqxdhDeploymentSessionAgreement` at the production codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and route `route′ = RawCtxFrameDecoding.sender reader.model` of item 7, Server identity index 0, with the probability of the CE experiment replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). The bounds, the bills and the premises are those of `PqxdhDeploymentProductionRegistration.ce_a1` and `ce_a1_billed`; the Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`). As in `PqxdhDeploymentSessionAgreement`, the event coincides with CE-A1's on the support, and root agreement, the payload and the assigned key ID are not stated. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionSessionAgreement

variable {ι KemSK Reader Response Message Root A X : Type} {baseSpec : OracleSpec ι}

section
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentServerAuth (serverAuthBound serverAuthAdversary reduction ReductionCaps)
open PqxdhDeploymentServerAuthBills (coinCap romCap hashCap totalCap)
open PqxdhDeploymentSessionAgreement (A1NoAgreement)

/-- Production form of `PqxdhDeploymentSessionAgreement.ce_a1_agreement` (O21 at the CE-A1 bound, ten of the eleven ServerAuth fields). The statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with the probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). The bound and the bills conjunct are those of `PqxdhDeploymentProductionRegistration.ce_a1` verbatim. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`); every other premise is the one of `ce_a1_agreement` at the production codec and route. -/
theorem ce_a1_agreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList)
      setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (qCoin Q qH qHash qTotal qFinish : Nat)
    (reductionCaps : ∀ c, ReductionCaps (reduction (KemSK := KemSK) setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) bounds mode
        adversary c)
      qCoin Q qH qHash qTotal qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => @decide (∃ c, A1NoAgreement setup (PqxdhBoundaryRecordPrelude.withReader codec reader) c
      outcome) (Classical.propDecidable _)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c) qCoin Q qH qHash fallback
            signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentSessionAgreement.ce_a1_agreement setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps bounded (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime qCoin Q qH qHash qTotal qFinish reductionCaps fallback
      signatureFallback

/-- Production form of `PqxdhDeploymentSessionAgreement.ce_a1_agreement_billed` (O21 at the transported deployment budget). The statement at the production codec and route, with the probability read back through `unwrap` on the classical source game (`PqxdhDeploymentProductionTransfer.chance`); the bound and the bills conjunct are those of `PqxdhDeploymentProductionRegistration.ce_a1_billed` verbatim. -/
theorem ce_a1_agreement_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => @decide (∃ c, A1NoAgreement setup (PqxdhBoundaryRecordPrelude.withReader codec reader) c
      outcome) (Classical.propDecidable _)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
        (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish fallback signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentSessionAgreement.ce_a1_agreement_billed setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded (RawCtxFrameDecoding.sender reader.model)
      ensureInit ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime fallback signatureFallback

end

end BeaconcryptCore.Computational.PqxdhDeploymentProductionSessionAgreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionSessionAgreement.ce_a1_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionSessionAgreement.ce_a1_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionSessionAgreement.ce_a1_agreement_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionSessionAgreement.ce_a1_agreement_billed
