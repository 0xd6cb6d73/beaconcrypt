-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawTargetMarked
import BeaconcryptCore.Computational.CborRawStartupEquality

/-! Actual native target decisions derive the selected-session mark from their own accept/bundle witnesses. The initialized source slot and complete counted raw World therefore have equal event probabilities. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawTargetSlot
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget Handle)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentEnvironmentJoin (uncount)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentIdealHandoff (decisionOn)
open CborRawPublicState (Public)
open CborRawIdealWorldProgram (after fixedClient)
open CborRawHeadlineSlot (observe birth fixed_event after_event)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (event : Observed X → Bool) (claim : Observed X → Option Handle)
/-- Actual raw target decisions retain their derived mark, so native-to-World transport is exact. -/
theorem marked_world (parameters : Params KemSK budget.create)
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (created : PqxdhLiveServerConstruction.Created Unit) (world : PqxdhRecordLiftWorld.State 2)
    (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    𝒟[CborRawMarkedPrefix.run setup wire parse checks (Target.ofCE budget g) parameters created (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2))
      (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
        PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))] {true} =
      𝒟[observe (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
        (CborRawCompile.route parse))
        (after setup wire parse checks (Target.ofCE budget g) ensureInit runtime parameters created (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))).run world] {true} := by
  rw [CborRawTargetMarked.marked_eq setup wire parse checks nativePhase1 budget g parameters created bounds mode
    adversary event claim]
  have joined := (CborRawWorldCoreHandoff.middle_world_from setup wire parse checks (Target.ofCE budget g) parameters created ensureInit 0
    runtime world fresh (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩ : Public)).map
      (fun value => (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) (value.1, value.2.2.1))
  simp only [Functor.map_map] at joined
  rw [joined.evalDist_eq, CborRecordWorldSimulation.client_simulation]
  rw [after_event setup wire parse checks (Target.ofCE budget g) parameters ensureInit runtime (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) created world fresh]

/-- The complete source slot and counted raw World agree for their actual per-target decision. -/
theorem slot_world (parameters : Params KemSK budget.create)
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (respects : budget.Respects adversary)
    (world : PqxdhRecordLiftWorld.State 2) (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    𝒟[PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup (CborRawCompile.sourceCodec wire parse) checks
      ensureInit none (fun result => (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) (result.1, result.2.copies.produced))
      (CborRawCompile.compile setup wire parse (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary))) runtime budget.create (Target.ofCE budget g).kem (Target.ofCE budget g).accept 2 parameters] {true} =
      𝒟[observe (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
        (CborRawCompile.route parse))
        (fixedClient setup wire parse checks (Target.ofCE budget g) ensureInit runtime parameters (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))).run world] {true} := by
  have source := CborRawInitializedSlot.slot_native setup wire parse checks (Target.ofCE budget g) parameters phase1 phase2 ensureInit
    runtime (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) (PqxdhDeploymentCompileCaps.transported bounds budget)
    (CborRawCompileCaps.certified setup wire parse bounds mode adversary budget respects) rfl rfl
    (by rw [PqxdhDeploymentIdealParams.pool_length]; exact PqxdhDeploymentCompileCaps.transported_room bounds budget)
  rw [source.evalDist_eq, fixed_event setup wire parse checks (Target.ofCE budget g) parameters ensureInit runtime (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) world]
  have result := CborRawStartupEquality.bind_eq setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (birth setup ensureInit runtime)
    (fun born => match born.1 with
      | none => pure false
      | some created => CborRawMarkedPrefix.run setup wire parse checks (Target.ofCE budget g) parameters created (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2))
          (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
            PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
    (fun born current => match born.1 with
      | none => pure false
      | some created => observe (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) <$>
          (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
            (after setup wire parse checks (Target.ofCE budget g) ensureInit runtime parameters created (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))).run current) world (by
      intro born _ current same
      cases found : born.1 with
      | none => rfl
      | some created =>
          exact marked_world setup wire parse checks ensureInit runtime bounds mode adversary budget g event claim
            parameters nativePhase1 created current (same.trans fresh))
  convert result using 1
  rfl

/-- Challenger and constructor draws preserve the exact raw slot-to-World target event. -/
theorem drawn_world
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (respects : budget.Respects adversary) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (fun result => (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) (result.1, result.2.copies.produced)) (CborRawCompile.compile setup wire parse (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))
      runtime budget.create (Target.ofCE budget g).kem (Target.ofCE budget g).accept 2] {true} =
      𝒟[observe (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
        (CborRawCompile.route parse))
        (CborRawIdealWorldProgram.client setup wire parse checks (Target.ofCE budget g) ensureInit runtime (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))).run
          PqxdhRecordLiftWorld.initial] {true} := by
  rw [PqxdhDeploymentIdealParams.slotGame_pool setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
    (fun result => (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) (result.1, result.2.copies.produced)) (CborRawCompile.compile setup wire parse (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary))) runtime
      budget.create (Target.ofCE budget g).kem (Target.ofCE budget g).accept 2]
  rw [CborRawIdealWorldProgram.client, simulateQ_bind, StateT.run_bind, map_bind, CborRawHeadlineStartup.guarded_coins]
  have result := CborRawStartupEquality.bind_eq setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (PqxdhDeploymentIdealParams.drawParams setup budget.create)
    (fun parameters => PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup
      (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (fun result => (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) (result.1, result.2.copies.produced)) (CborRawCompile.compile setup wire parse (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))
      runtime budget.create (Target.ofCE budget g).kem (Target.ofCE budget g).accept 2 parameters)
    (fun parameters world => observe (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
        (fixedClient setup wire parse checks (Target.ofCE budget g) ensureInit runtime parameters (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))).run world)
    PqxdhRecordLiftWorld.initial (by
      intro parameters _ world fresh
      exact slot_world setup wire parse checks ensureInit runtime bounds mode adversary budget g event claim parameters
        nativePhase1 phase1 phase2 respects world fresh)
  convert result using 1

end BeaconcryptCore.Computational.CborRawTargetSlot
/-- info: 'BeaconcryptCore.Computational.CborRawTargetSlot.marked_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetSlot.marked_world
/-- info: 'BeaconcryptCore.Computational.CborRawTargetSlot.slot_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetSlot.slot_world
/-- info: 'BeaconcryptCore.Computational.CborRawTargetSlot.drawn_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetSlot.drawn_world
