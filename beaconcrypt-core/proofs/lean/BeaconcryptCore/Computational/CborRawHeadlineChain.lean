-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawKemTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain

/-! The concrete per-target raw-CBOR security chain through KEM and the two-entry root/key-schedule hybrids. Every reduction consumes the actual raw compiler and its original wire ledger. The existing source14 caps and primitive losses are preserved; no old decoded-event correspondence is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineChain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget Handle)
open PqxdhDeploymentKemTransfer (Observed happens designated selectedKem)
open CborRawCompileSecrecy (compileFull)
open CborRawKemTransfer (decision)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

noncomputable def kemLoss (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (target : Fin budget.accept × Fin budget.capacity) (runtime : A) : ℝ :=
  (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
      (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (PqxdhRegistrationJointKemRawCertified.adversary setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim target)
      (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget target)
      target.1.val).toINDCCA).toReal + PqxdhRegistrationJointKemRawGame.correctnessError setup

noncomputable def slotLoss (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (target : Fin budget.accept × Fin budget.capacity) (runtime : A) : ℝ :=
  PqxdhRegistrationJointKemKeyTransfer.allIdealLoss setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
    (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim target)
    (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget target) target.1.val
    (PqxdhDeploymentCompileCaps.transported bounds budget)

/-- The actual raw-CBOR per-target event transfers to the certified KEM reduction, with its actual raw compiler and unchanged concrete caps. -/
theorem kem_transfer (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (target : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some target)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
        (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim target)
        (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget target)
        target.1.val false] {true} +
      ENNReal.ofReal (kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) := by
  rw [CborRawKemTransfer.eligible_actual setup wire parse checks lengths parser ensureInit phase1 phase2 bounds mode
    adversary budget event claim target runtime, ← PqxdhRegistrationJointKemRawOpaque.branchRaw_opaque]
  exact (PqxdhRegistrationJointKemRawBridge.actual_le_real setup (CborRawCompile.sourceCodec wire parse) checks
    ensureInit none _ (compileFull setup wire parse bounds mode adversary) runtime
    (PqxdhDeploymentCompileCaps.transported bounds budget)
    (CborRawCompileCaps.certified setup wire parse bounds mode adversary budget respects) budget.create
    (selectedKem budget target) target.1.val (PqxdhDeploymentCompileCaps.transported_room bounds budget)).trans
    (PqxdhRegistrationJointKemRawCertified.real_le_ideal setup functional (CborRawCompile.sourceCodec wire parse)
      checks ensureInit none _ _ runtime budget.create (selectedKem budget target) target.1.val)

/-- The actual raw event reaches the two-entry ideal slot game with the same KEM and root/key-schedule primitive losses. -/
theorem chain_slot (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (target : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some target)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
        (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim target)
        (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget target)
        target.1.val 2] {true} +
      ENNReal.ofReal (kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) +
      ENNReal.ofReal (slotLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) := by
  have first := kem_transfer setup functional wire parse checks lengths parser ensureInit phase1 phase2 bounds mode
    adversary budget respects event claim target runtime
  have keys := PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss setup (CborRawCompile.sourceCodec wire parse)
    checks ensureInit none (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim target)
    (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget target) target.1.val
    (PqxdhDeploymentCompileCaps.transported bounds budget)
    (CborRawCompileCaps.certified setup wire parse bounds mode adversary budget respects) correct
  rw [← PqxdhRegistrationJointBeaconFinishOnce.slotGame_two] at keys
  refine first.trans ?_
  have hop := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim target)
      (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget target) target.1.val false)
    (PqxdhRegistrationJointKemSecondEntry.slotGame setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim target)
      (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget target) target.1.val 2)
  calc _ ≤ _ := add_le_add hop le_rfl
    _ ≤ _ := by
      rw [add_right_comm]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal keys)

end BeaconcryptCore.Computational.CborRawHeadlineChain

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineChain.kem_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineChain.kem_transfer

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineChain.chain_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineChain.chain_slot
