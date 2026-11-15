-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawTargetMarked
import BeaconcryptCore.Computational.CborRawStartupEquality

/-! Actual native target decisions derive the selected-session mark from their own accept/bundle witnesses. The initialized source slot and complete counted raw World therefore have equal event probabilities. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
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
private noncomputable def recordBirth : ProbComp (Option (PqxdhLiveServerConstruction.Created PqxdhTranscriptAd.AssociatedData) ×
    PqxdhRegistrationJointServerPrefix.State KemSK A) :=
  (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)

private theorem birth_erase :
    (fun result => (result.1.map PqxdhDeploymentEnvironment.eraseCreatedMetadata, result.2)) <$>
      recordBirth setup ensureInit runtime = birth setup ensureInit runtime := by
  simp only [recordBirth, birth, PqxdhRegistrationJointServerBirth.source, StateT.run,
    PqxdhLiveServerConstruction.construct, Functor.map_map, map_bind]
  refine bind_congr fun ready => ?_
  split <;> simp only [map_pure, Functor.map_map] <;> rfl

/-- Actual raw target decisions retain their derived mark, so native-to-World transport is exact. -/
theorem marked_world (parameters : Params KemSK budget.create)
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (created : PqxdhLiveServerConstruction.Created PqxdhTranscriptAd.AssociatedData)
    (afterBirth : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, afterBirth) ∈ support (recordBirth setup ensureInit runtime))
    (world : PqxdhRecordLiftWorld.State 2)
    (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    𝒟[CborRawMarkedPrefix.run setup wire parse checks (Target.ofCE budget g) parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2))
      (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
        PqxdhDeploymentBackend.xinitial (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) (PqxdhDeploymentIdealSteps.idealInit (PqxdhDeploymentEnvironment.eraseCreatedMetadata created)))] {true} =
      𝒟[observe (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
        (CborRawCompile.route parse))
        (after setup wire parse checks (Target.ofCE budget g) ensureInit runtime parameters created (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))).run world] {true} := by
  have actualConstructor := (PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit
    setup.serverKeyId none ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
    afterBirth created born).2
  have initializedSame : CborRawIdealProvenanceStartup.initialized created world =
      PqxdhDeploymentEnvironmentJoin.initialized (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) world := by
    obtain ⟨seed, canonical, _⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit
      0 setup.serverKeyId none runtime afterBirth.2 created actualConstructor
    subst created
    rfl
  rw [CborRawTargetMarked.marked_eq setup wire parse checks nativePhase1 budget g parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) bounds mode
    adversary event claim]
  have joined := (CborRawWorldCoreHandoff.middle_world_from setup wire parse checks (Target.ofCE budget g) parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) ensureInit 0
    runtime world fresh (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩ : Public)).map
      (fun value => (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) (value.1, value.2.2.1))
  simp only [Functor.map_map] at joined
  rw [joined.evalDist_eq, CborRecordWorldSimulation.client_simulation]
  rw [after_event setup wire parse checks (Target.ofCE budget g) parameters ensureInit runtime (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) created world fresh, initializedSame]

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
  change 𝒟[birth setup ensureInit runtime >>= _] {true} = _
  rw [← birth_erase setup ensureInit runtime, bind_map_left]
  have result := CborRawStartupEquality.bind_eq setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (recordBirth setup ensureInit runtime)
    (fun born => match born.1 with
      | none => pure false
      | some created => CborRawMarkedPrefix.run setup wire parse checks (Target.ofCE budget g) parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)) (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2))
          (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
            PqxdhDeploymentBackend.xinitial (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) (PqxdhDeploymentIdealSteps.idealInit (PqxdhDeploymentEnvironment.eraseCreatedMetadata created))))
    (fun born current => match born.1 with
      | none => pure false
      | some created => observe (fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)) <$>
          (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
            (after setup wire parse checks (Target.ofCE budget g) ensureInit runtime parameters created (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)))).run current) world (by
      intro born supported current same
      cases found : born.1 with
      | none => rfl
      | some created =>
          exact marked_world setup wire parse checks ensureInit runtime bounds mode adversary budget g event claim
            parameters nativePhase1 created born.2 (by
              change (born.1, born.2) ∈ support (recordBirth setup ensureInit runtime) at supported
              rw [found] at supported
              exact supported) current (same.trans fresh))
  convert result using 1
  · congr 1
    apply congrArg evalDist
    apply bind_congr
    rintro ⟨_ | created, afterBirth⟩ <;> rfl
  · rfl

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
