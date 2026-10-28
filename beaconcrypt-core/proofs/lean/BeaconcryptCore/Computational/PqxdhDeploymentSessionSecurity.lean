-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling
import BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt

/-! Complete root, assigned-identifier and payload agreement for the private target-prefix extension of the deployment experiment. The extension uses the existing CE-A1 reduction on its actual generation and callback receipts; SessionCoupling.frozen_root_state supplies its full native-state projection. No agreement witness is supplied by the caller and no additional cryptographic assumption is introduced. -/

open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentServerAuth (reduction serverAuthAdversary serverAuthBound ReductionCaps)
open PqxdhDeploymentServerAuthBills (coinCap romCap hashCap totalCap)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

/-- The complete compiled result together with the actual generation and private root receipts. -/
abbrev Outcome (KemSK X : Type) := PqxdhRegistrationR1RootAudit.RootAudit KemSK
  (PqxdhDeploymentSessionCoupling.ReducedResult KemSK
    ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local))

/-- The real generated Server seed followed by the root-labelled target prefix of the compiled complete deployment interface. The private annotation never enters the adversary's replies. -/
noncomputable def generated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) :
    ProbComp (Outcome KemSK X) := do
  let seed ← sampleSeed
  PqxdhDeploymentSessionCoupling.audited setup codec checks seed c
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)

/-- Failure means an actual acceptance without complete source root and delivered-record agreement. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (outcome : Outcome KemSK X) : Bool :=
  @decide (PqxdhDeploymentSessionReceipt.Failure setup codec checks outcome.2) (Classical.propDecidable _)

/-- The same root-labelled deployment prefix, with only the client's return value discarded, is the existing production-order CE-A1 source experiment. -/
theorem generated_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) :
    Prod.snd <$> generated setup codec checks route bounds mode adversary c =
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary setup codec route bounds mode adversary c) := by
  have same := PqxdhRegistrationR1RootAudit.generated_order setup codec checks
    (reduction (KemSK := KemSK) setup codec route bounds mode adversary c)
  simp only [generated, map_bind]
  exact same

/-- Complete root and delivered-field failure is the existing CE-A1 source failure on the same execution. -/
theorem decision_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) :
    decision setup codec checks <$> generated setup codec checks route bounds mode adversary c =
      PqxdhServerAuthCommonProbability.decision setup codec checks <$>
        PqxdhServerAuthRootObserved.orderedGame setup codec checks false
          (serverAuthAdversary setup codec route bounds mode adversary c) := by
  rw [← generated_order setup codec checks route bounds mode adversary c, Functor.map_map]
  change (fun outcome : Outcome KemSK X =>
    @decide (PqxdhDeploymentSessionReceipt.Failure setup codec checks outcome.2) (Classical.propDecidable _)) <$> _ = _
  exact congrArg (fun f : Outcome KemSK X → Bool => f <$> generated setup codec checks route bounds mode adversary c)
    (funext fun outcome => decide_eq_decide.mpr
      (PqxdhDeploymentSessionReceipt.failure_iff setup codec checks outcome.2))

/-- Per creation index, complete root/identifier/payload agreement has the original CE-A1 authentication bound and all of its original reduction bills. No caller supplies a partner, root or successful-initialization witness. -/
theorem complete_agreement_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (c : Nat)
    (qCoin Q qH qHash qTotal qFinish : Nat)
    (reductionCaps : ReductionCaps (reduction (KemSK := KemSK) setup codec route bounds mode adversary c)
      qCoin Q qH qHash qTotal qFinish)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[decision setup codec checks <$> generated setup codec checks route bounds mode adversary c]
      {true}).toReal ≤
      serverAuthBound setup codec checks caps (serverAuthAdversary setup codec route bounds mode adversary c)
        qCoin Q qH qHash fallback signatureFallback ∧
    PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  rw [decision_order]
  exact PqxdhServerAuthCommonAuthentication.common_authentication_with_resources setup codec checks caps bounded
    (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash
    ((PqxdhRegistrationR1Authentication.budget_iff
      (reduction (KemSK := KemSK) setup codec route bounds mode adversary c) Q qH qHash).mpr reductionCaps.source)
    (fun input => (PqxdhRegistrationR1Authentication.unit_queries
      (reduction (KemSK := KemSK) setup codec route bounds mode adversary c) input _ _).mpr
        (reductionCaps.coins input))
    law spread correct adapter writable phase2 frameBack qTotal qFinish
    (fun input => by
      simpa only [serverAuthAdversary, PqxdhRegistrationR1Authentication.unitWork, IsTotalQueryBound,
        isQueryBound_map_iff] using reductionCaps.total input)
    (fun input => (PqxdhRegistrationR1Authentication.unit_queries
      (reduction (KemSK := KemSK) setup codec route bounds mode adversary c) input _ _).mpr
        (reductionCaps.finish input)) fallback signatureFallback

/-- Complete agreement with every reduction cap discharged from the original complete-interface budget, counting rejected attempts as before. -/
theorem complete_agreement_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (c : Nat)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[decision setup codec checks <$> generated setup codec checks route bounds mode adversary c]
      {true}).toReal ≤
      serverAuthBound setup codec checks caps (serverAuthAdversary setup codec route bounds mode adversary c)
        (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) fallback signatureFallback ∧
    PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish fallback signatureFallback :=
  complete_agreement_bound setup codec checks caps bounded route bounds mode adversary c
    (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
    budget.finish
    (PqxdhDeploymentServerAuthBills.reduction_caps setup codec caps bounded route bounds mode adversary budget
      respects c) law spread correct adapter writable phase2 frameBack fallback signatureFallback

end BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.generated_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.generated_order

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.decision_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.decision_order

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.complete_agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.complete_agreement_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.complete_agreement_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity.complete_agreement_billed
