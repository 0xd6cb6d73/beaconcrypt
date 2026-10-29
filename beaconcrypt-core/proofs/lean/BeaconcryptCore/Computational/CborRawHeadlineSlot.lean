-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealWorldProgram
import BeaconcryptCore.Computational.CborRawMarkedBound

/-! The initialized two-entry raw source slot game reaches the actual guarded record World. Constructor draws remain counted World requests, every native failure is retained, and the private selected-session mark is removed only by Boolean event containment. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineSlot
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentEnvironmentJoin (uncount initialized)
open CborRawPublicState (Public)
open CborRawIdealWorldProgram (Output after fixedClient)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}

def observe {count : Nat} (event : Result × CborRawPostActive.Produced → Bool)
    (result : Output KemSK Result count × PqxdhRecordLiftWorld.State 2) : Bool :=
  result.1.any fun value => event (value.2.1, result.2.produced)

section Slot
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (work : OracleComp Spec Result) (event : Result × CborRawPostActive.Produced → Bool)

noncomputable def birth : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit) ×
    PqxdhRegistrationJointServerPrefix.State KemSK A) :=
  (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)

/-- The exact source constructor draws are counted before the fixed raw continuation. -/
theorem fixed_event (world : PqxdhRecordLiftWorld.State 2) :
    observe event <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse))
      (fixedClient setup wire parse checks target ensureInit runtime parameters work)).run world =
      (CborRawHeadlineStartup.coins setup (boundaryWire wire parse) (CborRawCompile.route parse)
        (birth setup ensureInit runtime) world >>= fun born =>
        match born.1.1 with
        | none => pure false
        | some created => observe event <$>
            (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
              (after setup wire parse checks target ensureInit runtime parameters created work)).run born.2) := by
  simp only [fixedClient, simulateQ_bind, StateT.run_bind, map_bind]
  rw [CborRawHeadlineStartup.guarded_coins]
  apply bind_congr
  intro born
  cases found : born.1.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure, observe, Option.any_none]
  | some created => simp only []

/-- Actual Server initialization followed by the fixed raw continuation retains precisely its result and produced frames. -/
theorem after_event (created : PqxdhLiveServerConstruction.Created Unit) (world : PqxdhRecordLiftWorld.State 2)
    (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    observe event <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse))
      (after setup wire parse checks target ensureInit runtime parameters created work)).run world =
      (fun value => event (value.1.1, value.2.produced)) <$>
        (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
          ((simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
            (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters ensureInit
              0 runtime) setup.serverKeyId)) work).run
              (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
                PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created)))).run
                  (initialized created world) := by
  have vacant : world.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
  have bornRun : (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse) (.inl created)).run world = pure ((), initialized created world) := by
    change PqxdhRecordLiftWorld.initializeServer created world = _
    simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
    rfl
  rw [after, simulateQ_bind, StateT.run_bind, simulateQ_spec_query, bornRun, pure_bind]
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- Every actual marked native execution is bounded by the initialized actual raw World event. -/
theorem marked_world (created : PqxdhLiveServerConstruction.Created Unit) (world : PqxdhRecordLiftWorld.State 2)
    (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    𝒟[CborRawMarkedPrefix.run setup wire parse checks target parameters created work event
      (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
        PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))] {true} ≤
      𝒟[observe event <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
        (CborRawCompile.route parse))
        (after setup wire parse checks target ensureInit runtime parameters created work)).run world] {true} := by
  have bounded := CborRawMarkedBound.marked_le setup wire parse checks target parameters created work event
    (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
      PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))
  have joined := (CborRawWorldCoreHandoff.middle_world_from setup wire parse checks target parameters created ensureInit 0
    runtime world fresh work (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩ : Public)).map
      (fun value => event (value.1, value.2.2.1))
  simp only [Functor.map_map] at joined
  rw [joined.evalDist_eq, CborRecordWorldSimulation.client_simulation] at bounded
  rw [after_event setup wire parse checks target parameters ensureInit runtime work event created world fresh]
  exact bounded

/-- The complete initialized source slot game is bounded by its actual counted raw record-World event. -/
theorem slot_world
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (bounded : ∀ kind, (CborRawCompile.compile setup wire parse work).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (parameters.pool target).length)
    (world : PqxdhRecordLiftWorld.State 2) (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    𝒟[PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup (CborRawCompile.sourceCodec wire parse) checks
      ensureInit none (fun result => event (result.1, result.2.copies.produced))
      (CborRawCompile.compile setup wire parse work) runtime count target.kem target.accept 2 parameters] {true} ≤
      𝒟[observe event <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
        (CborRawCompile.route parse))
        (fixedClient setup wire parse checks target ensureInit runtime parameters work)).run world] {true} := by
  have source := CborRawInitializedSlot.slot_native setup wire parse checks target parameters phase1 phase2 ensureInit
    runtime work event budget bounded unreadIdentity unreadKem room
  rw [source.evalDist_eq, fixed_event setup wire parse checks target parameters ensureInit runtime work event world]
  have result := CborRawHeadlineStartup.bind_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (birth setup ensureInit runtime)
    (fun born => match born.1 with
      | none => pure false
      | some created => CborRawMarkedPrefix.run setup wire parse checks target parameters created work event
          (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
            PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
    (fun born current => match born.1 with
      | none => pure false
      | some created => observe event <$>
          (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
            (after setup wire parse checks target ensureInit runtime parameters created work)).run current) world (by
      intro born _ current same
      cases found : born.1 with
      | none => exact le_rfl
      | some created =>
          exact marked_world setup wire parse checks target parameters ensureInit runtime work event created current
            (same.trans fresh))
  convert result using 1
  rfl

end Slot

/-- Drawing the challenger parameters and the actual Server constructor preserves the complete raw slot-to-World upper bound. -/
theorem drawn_world (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (work : OracleComp Spec Result) (event : Result × CborRawPostActive.Produced → Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (bounded : ∀ kind, (CborRawCompile.compile setup wire parse work).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0) (room : budget (.inl 1) ≤ count + 1) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (fun result => event (result.1, result.2.copies.produced)) (CborRawCompile.compile setup wire parse work)
      runtime count target.kem target.accept 2] {true} ≤
      𝒟[observe event <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
        (CborRawCompile.route parse))
        (CborRawIdealWorldProgram.client setup wire parse checks target ensureInit runtime work)).run
          PqxdhRecordLiftWorld.initial] {true} := by
  rw [PqxdhDeploymentIdealParams.slotGame_pool setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
    (fun result => event (result.1, result.2.copies.produced)) (CborRawCompile.compile setup wire parse work) runtime
      count target.kem target.accept 2]
  rw [CborRawIdealWorldProgram.client, simulateQ_bind, StateT.run_bind, map_bind, CborRawHeadlineStartup.guarded_coins]
  have result := CborRawHeadlineStartup.bind_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (PqxdhDeploymentIdealParams.drawParams setup count)
    (fun parameters => PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup
      (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (fun result => event (result.1, result.2.copies.produced)) (CborRawCompile.compile setup wire parse work)
      runtime count target.kem target.accept 2 parameters)
    (fun parameters world => observe event <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
        (fixedClient setup wire parse checks target ensureInit runtime parameters work)).run world)
    PqxdhRecordLiftWorld.initial (by
      intro parameters _ world fresh
      exact slot_world setup wire parse checks target parameters ensureInit runtime work event phase1 phase2 budget bounded
        unreadIdentity unreadKem (by rw [PqxdhDeploymentIdealParams.pool_length]; exact room) world fresh)
  convert result using 1

end BeaconcryptCore.Computational.CborRawHeadlineSlot

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlot.fixed_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlot.fixed_event

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlot.after_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlot.after_event

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlot.marked_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlot.marked_world

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlot.slot_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlot.slot_world

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlot.drawn_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlot.drawn_world
