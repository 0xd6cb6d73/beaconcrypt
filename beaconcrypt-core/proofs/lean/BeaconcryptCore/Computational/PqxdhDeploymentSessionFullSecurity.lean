-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution

/-! Complete session agreement in one whole adaptive deployment-source run. A private root receipt is retained at the target's acceptance prefix and every actual later source callback still executes. Forgetting the receipt preserves the complete original result and native final state; the failure event has precisely the original CE-A1 primitive losses and bills. -/

open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentServerAuth (reduction serverAuthAdversary serverAuthBound ReductionCaps)
open PqxdhDeploymentServerAuthBills (coinCap romCap hashCap totalCap)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

abbrev SourceResult (X : Type) := (X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local
abbrev Outcome (KemSK X : Type) := PqxdhDeploymentSessionFullExecution.PrefixAudit KemSK (SourceResult X) ×
  (SourceResult X × PqxdhRegistrationSchedule.State KemSK)

/-- One actual generated Server, private target receipt and full real adaptive source continuation. -/
noncomputable def generated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) : ProbComp (Outcome KemSK X) := do
  let seed ← sampleSeed
  PqxdhDeploymentSessionFullExecution.full setup codec checks seed c
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)

/-- The same complete root/identifier/payload failure decision, read from the private prefix of the whole real execution. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (outcome : Outcome KemSK X) : Bool :=
  PqxdhServerAuthCommonProbability.decision setup codec checks outcome.1.2

/-- The decision concerns actual acceptance without all root, initializer, assigned-ID, payload and AD receipts. -/
theorem decision_spec (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (outcome : Outcome KemSK X) :
    decision setup codec checks outcome = true ↔
      PqxdhDeploymentSessionReceipt.Failure setup codec checks outcome.1.2 := by
  simp only [decision, PqxdhServerAuthCommonProbability.decision, decide_eq_true_eq,
    PqxdhDeploymentSessionReceipt.failure_iff]

/-- The complete real continuation retains the original CE-A1 source-root marginal, with no conditioning on its success. -/
theorem root_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) :
    EvalDistEq ((fun outcome : Outcome KemSK X => outcome.1.2) <$>
      generated setup codec checks route bounds mode adversary c)
      (PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary setup codec route bounds mode adversary c)) := by
  have marginal := EvalDistEq.bind_right sampleSeed fun seed =>
    (PqxdhDeploymentSessionFullExecution.full_audit setup codec checks seed c
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).map Prod.snd
  have ordered := PqxdhRegistrationR1RootAudit.generated_order setup codec checks
    (fun input => PqxdhDeploymentServerAuthEmbed.adversary setup codec c
      (PqxdhDeploymentSessionResume.cut (PqxdhDeploymentServerAuthEmbed.stopAt c) []
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)) input)
  have unchanged : (fun input => (fun _ => ()) <$> PqxdhDeploymentServerAuthEmbed.adversary setup codec c
      (PqxdhDeploymentSessionResume.cut (PqxdhDeploymentServerAuthEmbed.stopAt c) []
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)) input) =
      serverAuthAdversary setup codec route bounds mode adversary c :=
    funext fun input => PqxdhDeploymentSessionFullExecution.adversary_cut_unit setup codec c
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) input
  rw [unchanged] at ordered
  rw [← ordered]
  simpa only [generated, map_bind, Functor.map_map, PqxdhDeploymentSessionCoupling.audited,
    PqxdhDeploymentServerAuthChain.seedInput] using marginal

/-- The stronger failure event in the full real run has exactly the existing CE-A1 source failure probability. -/
theorem decision_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) :
    EvalDistEq (decision setup codec checks <$> generated setup codec checks route bounds mode adversary c)
      (PqxdhDeploymentSessionSecurity.decision setup codec checks <$>
        PqxdhDeploymentSessionSecurity.generated setup codec checks route bounds mode adversary c) := by
  rw [PqxdhDeploymentSessionSecurity.decision_order]
  change EvalDistEq ((fun outcome : Outcome KemSK X =>
    PqxdhServerAuthCommonProbability.decision setup codec checks outcome.1.2) <$>
      generated setup codec checks route bounds mode adversary c) _
  simpa only [Functor.map_map] using
    (root_order setup codec checks route bounds mode adversary c).map
      (PqxdhServerAuthCommonProbability.decision setup codec checks)

/-- Erasing the root receipt preserves the actual complete compiled source execution, including the secrecy ledger, program result, all owners, both caches and the final native state. -/
theorem generated_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) :
    EvalDistEq (Prod.snd <$> generated setup codec checks route bounds mode adversary c)
      (do
        let seed ← sampleSeed
        Prod.map id PqxdhRegistrationR1Restriction.eraseShared <$>
          (simulateQ (PqxdhDeploymentServerAuthLocal.base setup codec checks seed)
            (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
              (PqxdhDeploymentSessionCoupling.initial setup seed)) := by
  simpa only [generated, map_bind] using EvalDistEq.bind_right sampleSeed (fun seed =>
    PqxdhDeploymentSessionFullExecution.full_erase setup codec checks seed c
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
      (PqxdhDeploymentServerAuthChain.compiled_unread setup codec route bounds mode adversary))

/-- In the same full real run, acceptance without root/assigned-ID/payload agreement is bounded by the original CE-A1 primitive reductions, with every cap discharged from the deployment budget. -/
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
      budget.finish fallback signatureFallback := by
  rw [(decision_order setup codec checks route bounds mode adversary c).evalDist_eq]
  exact PqxdhDeploymentSessionSecurity.complete_agreement_billed setup codec checks caps bounded route bounds mode
    adversary budget respects c law spread correct adapter writable phase2 frameBack fallback signatureFallback

end BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.decision_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.decision_spec

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.root_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.root_order

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.decision_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.decision_order

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.generated_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.generated_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.complete_agreement_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity.complete_agreement_billed
