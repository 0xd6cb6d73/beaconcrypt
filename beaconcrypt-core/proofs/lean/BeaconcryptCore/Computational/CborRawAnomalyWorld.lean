-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyInitialized
import BeaconcryptCore.Computational.CborRawAnomalyView
import BeaconcryptCore.Computational.CborRawHeadlineSlot

/-! The actual counted raw World continuation and native pool predictor have the same Boolean challenge-hit law. Startup counters remain in the World; the proved middle handoff forgets them only after all native effects and the complete original ledger have been retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawAnomalyWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentSecrecy (Ledger wrap)
open PqxdhDeploymentIdealGuess (guessCt)
open PqxdhDeploymentEnvironmentJoin (uncount initialized)
open CborTaggedSimulation (boundaryWire)
open CborRawIdealWorldProgram (Output after)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

noncomputable def observe (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) {count : Nat} (target : Target count)
    (result : Output KemSK (X × Ledger) count × PqxdhRecordLiftWorld.State 2) : Bool :=
  result.1.any fun value => decide (guessCt (boundaryWire wire parse) target value.2.1.2.transcript =
    some value.2.2.2.backend.1.challenge)

section Fixed
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)

private theorem source_erase (before : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => (result.1.map PqxdhDeploymentEnvironment.eraseCreatedMetadata, result.2)) <$>
      ((PqxdhRegistrationJointServerBirth.source (P := PqxdhTranscriptAd.AssociatedData) setup.joint ensureInit setup.serverKeyId none).run before) =
      ((PqxdhRegistrationJointServerBirth.source (P := Unit) setup.joint ensureInit setup.serverKeyId none).run before) := by
  simp only [PqxdhRegistrationJointServerBirth.source, StateT.run,
    PqxdhLiveServerConstruction.construct, Functor.map_map, map_bind]
  refine bind_congr fun ready => ?_
  split <;> simp only [map_pure, Functor.map_map] <;> rfl

/-- Actual Server initialization and parameter retention expose precisely the original full ledger hit event. -/
theorem after_observe (created : PqxdhLiveServerConstruction.Created PqxdhTranscriptAd.AssociatedData) (world : PqxdhRecordLiftWorld.State 2)
    (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    observe wire parse target <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse))
      (after setup wire parse checks target ensureInit runtime parameters created
        (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary)))).run world =
    (fun value => decide (guessCt (boundaryWire wire parse) target value.1.1.2.transcript = some parameters.challenge)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
        ((simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
          (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters ensureInit 0
            runtime) setup.serverKeyId))
          (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary))).run
            (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
              PqxdhDeploymentEnvironment.envInitial (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) (PqxdhDeploymentIdealSteps.splitInit (PqxdhDeploymentEnvironment.eraseCreatedMetadata created))))).run
                (CborRawIdealProvenanceStartup.initialized created world) := by
  have vacant : world.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
  have bornRun : (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse) (.inl created)).run world = pure ((), CborRawIdealProvenanceStartup.initialized created world) := by
    change PqxdhRecordLiftWorld.initializeServer created world = _
    simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
    rfl
  rw [after, simulateQ_bind, StateT.run_bind, simulateQ_spec_query, bornRun, pure_bind]
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map, observe]
  rfl

/-- The complete actual raw World hit event is bounded by the native raw pool hit using actual Server-construction support. -/
theorem after_pool (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (created : PqxdhLiveServerConstruction.Created PqxdhTranscriptAd.AssociatedData)
    (before afterState : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, afterState) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run before))
    (world : PqxdhRecordLiftWorld.State 2) (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    𝒟[observe wire parse target <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse))
      (after setup wire parse checks target ensureInit runtime parameters created
        (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary)))).run world]
      {true} =
    𝒟[(fun guessed => decide (guessed = some parameters.challenge)) <$>
      CborRawAnomalyPool.atPool setup wire parse checks target parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) bounds mode adversary] {true} := by
  have actualConstructor := (PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit
    setup.serverKeyId none before afterState created born).2
  have initializedSame : CborRawIdealProvenanceStartup.initialized created world =
      initialized (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) world := by
    obtain ⟨seed, canonical, _⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit
      before.1.1.seeds.length setup.serverKeyId none before.2 afterState.2 created actualConstructor
    subst created
    rfl
  have erasedBorn : (some (PqxdhDeploymentEnvironment.eraseCreatedMetadata created), afterState) ∈ support
      ((PqxdhRegistrationJointServerBirth.source (P := Unit) setup.joint ensureInit setup.serverKeyId none).run before) := by
    rw [← source_erase setup ensureInit before, support_map]
    exact ⟨(some created, afterState), born, rfl⟩
  rw [after_observe setup wire parse checks target parameters ensureInit runtime bounds mode adversary created world fresh, initializedSame]
  have joined := (CborRawWorldCoreHandoff.middle_world_from setup wire parse checks target parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) ensureInit
    0 runtime world fresh
    (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary))
    (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩ : CborRawPublicState.Public)).map
      (fun value => decide (guessCt (boundaryWire wire parse) target value.1.2.transcript = some parameters.challenge))
  have guessed := (CborRawAnomalyInitialized.middle_pool setup wire parse checks lengths parser phase1 phase2 target
    parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata created) ensureInit before afterState erasedBorn bounds mode adversary).map
      (fun value => decide (value = some parameters.challenge))
  simp only [Functor.map_map] at joined guessed
  rw [CborRecordWorldSimulation.client_simulation] at joined
  rw [← joined.evalDist_eq]
  simp only [CborRawPublicState.ofMemory, CborAdmissionCompiler.Local.empty, PqxdhDeploymentCompile.Local.empty] at guessed
  rw [guessed.evalDist_eq]

end Fixed
end BeaconcryptCore.Computational.CborRawAnomalyWorld

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyWorld.after_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyWorld.after_observe
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyWorld.after_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyWorld.after_pool
