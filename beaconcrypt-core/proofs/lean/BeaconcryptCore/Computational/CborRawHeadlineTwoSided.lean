-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawTargetSlot
import BeaconcryptCore.Computational.CborRawKemTwoSided

/-! Exact raw slot/record-World transport and the two-sided KEM/root hybrid telescope preserve arbitrary per-target decisions, including left-or-right guesses. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineTwoSided
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget Handle)
open PqxdhDeploymentKemTransfer (Observed happens designated selectedKem)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (viewObserved decisionOn)
open PqxdhRecordLiftIdeal (chainView)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The actual source slot and complete counted raw record World give equal probabilities for every per-target decision. -/
theorem slot_real_eq (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (CborRawKemTransfer.decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g)
      (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) runtime budget.create
      (selectedKem budget g) g.1.val 2] {true} =
    𝒟[(fun view => (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget event claim g)) <$>
      (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup (boundaryWire wire parse)
        (CborRawCompile.route parse) (CborRawRecordLiftBounds.client (CborRawEnvironment.environment
          (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks (Target.ofCE budget g)
            ensureInit 0 runtime) setup.serverKeyId) setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
              mode adversary))] {true} := by
  let work := PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)
  let chosen : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced → Bool := fun result =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)
  have bounded := CborRawTargetSlot.drawn_world setup wire parse checks ensureInit runtime bounds mode adversary budget g event claim
    nativePhase1 phase1 phase2 respects
  rw [← CborRawIdealWorldProgram.program setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode
    adversary] at bounded
  unfold CborRawHeadlineSlot.observe at bounded
  rw [CborRawHeadlineWorld.real_event setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (CborRawEnvironment.environment (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks
      (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId) setup.serverKeyId bounds mode adversary chosen] at bounded
  convert bounded using 1
  · rfl
  · congr 2
    congr 1
    funext view
    simp only [viewObserved, Option.any_map]
    rfl


/-- The actual raw event is within the concrete KEM and root/key-schedule losses of its two-entry source slot. -/
theorem chain_slot_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      (𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
        (CborRawKemTransfer.decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g)
        (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val 2]
          {true}).toReal| ≤
      CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim g runtime +
        CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget event claim g runtime := by
  have kem := CborRawKemTwoSided.kem_transfer setup functional wire parse checks lengths parser ensureInit phase1
    phase2 bounds mode adversary budget respects event claim g runtime
  have item2 := PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
    (CborRawKemTransfer.decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g)
    (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) runtime budget.create
    (selectedKem budget g) g.1.val (PqxdhDeploymentCompileCaps.transported bounds budget)
    (CborRawCompileCaps.certified setup wire parse bounds mode adversary budget respects) correct
  rw [← PqxdhRegistrationJointBeaconFinishOnce.slotGame_two] at item2
  exact (abs_sub_le _ _ _).trans (add_le_add kem item2)


/-- The complete raw experiment and actual cursor-compiled record World are two-sided close with their concrete source losses. -/
theorem chain_real_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (target : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some target)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true}).toReal -
      (𝒟[(fun view => (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget event claim target)) <$>
        (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup (boundaryWire wire parse)
          (CborRawCompile.route parse) (CborRawRecordLiftBounds.client (CborRawEnvironment.environment
            (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks (Target.ofCE budget target)
              ensureInit 0 runtime) setup.serverKeyId) setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
                mode adversary))] {true}).toReal| ≤
      CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime +
      CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime := by
  have close := chain_slot_close setup functional wire parse checks lengths parser ensureInit phase1 phase2 correct bounds
    mode adversary budget respects event claim target runtime
  rw [slot_real_eq setup wire parse checks phase1 phase2 nativePhase1 ensureInit bounds mode adversary budget respects
    event claim target runtime] at close
  exact close

end BeaconcryptCore.Computational.CborRawHeadlineTwoSided
/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineTwoSided.slot_real_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineTwoSided.slot_real_eq
/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineTwoSided.chain_slot_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineTwoSided.chain_slot_close
/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineTwoSided.chain_real_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineTwoSided.chain_real_close
