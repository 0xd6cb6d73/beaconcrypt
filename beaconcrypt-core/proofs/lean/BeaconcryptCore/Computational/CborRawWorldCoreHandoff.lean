-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawGuardedChain

/-! The independently defined native raw middle game is the actual raw record-world client, at the complete public result/registration-state/produced-frame view. The proof composes the concrete ideal-to-split chain with the derived initialized environment join. It keeps the original secrecy program above admission and introduces no event-simulation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawWorldCoreHandoff
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealKeys (splitView)
open CborRawPublicState (Public)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}

private theorem view_produced {S : Type} (state : XState KemSK (PqxdhDeploymentIdealSteps.IdealBk S) 2) :
    (splitView state).1.produced = state.base.produced := rfl

section Handoff
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)

private theorem view_core {S : Type} (state : XState KemSK (PqxdhDeploymentIdealSteps.IdealBk S) 2) :
    (splitView state).2.1.2 = state.backend.2.2 := rfl

/-- Every adaptive native raw ideal program has the actual guarded record-world execution at its full public observation, using independent source registration and ordinary record codecs. -/
theorem native_world (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (work : OracleComp Spec Result) (publicState : Public) :
    LawEq ((fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2)) <$>
        (simulateQ (CborRawNativePublic.native setup wire parse checks target parameters created) work).run
          (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
      ((fun value => (value.1.1, value.1.2.1, value.2.produced, value.1.2.2.backend.2.2)) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
            (CborRawCompile.route parse))
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
              (CborRawEnvironment.environment
                (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
                  ensureInit identityIndex runtime) setup.serverKeyId)) work).run
                    (publicState, PqxdhDeploymentEnvironment.envInitial created
                      (PqxdhDeploymentIdealSteps.splitInit created)))
            (CborRecordWorldCursor.worldShell (PqxdhDeploymentEnvironmentJoin.initialized created
              (PqxdhRecordLiftWorld.initial (n := 2)))))).run
                (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := 2)))) := by
  have changed := (CborRawGuardedChain.ideal_to_split setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse) checks target parameters created
    (CborRawPublicClient.client work publicState)).map
      (fun value => (value.1.1, value.1.2, value.2.1.produced, value.2.2.1.2))
  simp only [Functor.map_map, view_produced, view_core, CborRawPublicClient.client,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT] at changed
  have joined := (CborRawEnvironmentRun.ideal_initialized setup wire parse checks target parameters ensureInit
    identityIndex runtime created work publicState).map (fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2))
  simp only [Functor.map_map, PqxdhDeploymentEnvironmentJoin.merge] at joined
  simpa only [CborRawNativePublic.native, CborRawEnvironmentRun.handler] using changed.trans joined.symm

/-- The source-independent raw middle handler and the actual initialized record-world client agree on every public outcome, including failure replies, produced frames and the complete ideal registration core. -/
theorem middle_world (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (work : OracleComp Spec Result) (publicState : Public) :
    LawEq ((fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2)) <$>
        (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) work).run
          (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
      ((fun value => (value.1.1, value.1.2.1, value.2.produced, value.1.2.2.backend.2.2)) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
            (CborRawCompile.route parse))
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
              (CborRawEnvironment.environment
                (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
                  ensureInit identityIndex runtime) setup.serverKeyId)) work).run
                    (publicState, PqxdhDeploymentEnvironment.envInitial created
                      (PqxdhDeploymentIdealSteps.splitInit created)))
            (CborRecordWorldCursor.worldShell (PqxdhDeploymentEnvironmentJoin.initialized created
              (PqxdhRecordLiftWorld.initial (n := 2)))))).run
                (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := 2)))) := by
  have exactRun := congrArg (fun program => (fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2)) <$> program)
    (CborRawNativePublic.run setup wire parse checks target parameters created work
      (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq, CborRawNativePublic.reset,
    PqxdhDeploymentIdealCut.unghost] at exactRun
  refine (LawEq.of_eq exactRun.symm).trans ?_
  exact native_world setup wire parse checks target parameters created ensureInit identityIndex runtime work publicState

/-- Startup accounting is retained from any actual fresh World state; its counted coins are never reset. -/
theorem native_world_from (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (startupWorld : PqxdhRecordLiftWorld.State 2)
    (fresh : PqxdhDeploymentEnvironmentJoin.uncount startupWorld =
      PqxdhDeploymentEnvironmentJoin.uncount (PqxdhRecordLiftWorld.initial (n := 2)))
    (work : OracleComp Spec Result) (publicState : Public) :
    LawEq ((fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2)) <$>
        (simulateQ (CborRawNativePublic.native setup wire parse checks target parameters created) work).run
          (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
      ((fun value => (value.1.1, value.1.2.1, value.2.produced, value.1.2.2.backend.2.2)) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
            (CborRawCompile.route parse))
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
              (CborRawEnvironment.environment
                (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
                  ensureInit identityIndex runtime) setup.serverKeyId)) work).run
                    (publicState, PqxdhDeploymentEnvironment.envInitial created
                      (PqxdhDeploymentIdealSteps.splitInit created)))
            (CborRecordWorldCursor.worldShell (PqxdhDeploymentEnvironmentJoin.initialized created
              startupWorld)))).run
                (PqxdhDeploymentEnvironmentJoin.initialized created startupWorld)) := by
  have changed := (CborRawGuardedChain.ideal_to_split setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse) checks target parameters created
    (CborRawPublicClient.client work publicState)).map
      (fun value => (value.1.1, value.1.2, value.2.1.produced, value.2.2.1.2))
  simp only [Functor.map_map, view_produced, view_core, CborRawPublicClient.client,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT] at changed
  have admissible := PqxdhDeploymentEnvironmentJoin.good_initial (KemSK := KemSK) created
    (PqxdhDeploymentIdealSteps.splitInit created) startupWorld fresh
  have inv : PqxdhDeploymentIdealEnv.IdealInv target
      (PqxdhDeploymentEnvironment.envInitial (KemSK := KemSK) created (PqxdhDeploymentIdealSteps.splitInit created))
      (PqxdhDeploymentEnvironmentJoin.initialized created startupWorld) :=
    PqxdhDeploymentIdealEnv.idealInv_stable target _ _ _
      (PqxdhDeploymentEnvironmentJoin.initialized_view created startupWorld fresh)
      (PqxdhDeploymentIdealEnv.idealInv_start target created)
  have fullJoin := CborRawEnvironmentRun.ideal_run_join setup wire parse checks target parameters ensureInit
    identityIndex runtime created work
    (publicState, PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created))
    (PqxdhDeploymentEnvironmentJoin.initialized created startupWorld) admissible inv
  rw [PqxdhDeploymentEnvironmentJoin.merge_initial created (PqxdhDeploymentIdealSteps.splitInit created)
    startupWorld fresh] at fullJoin
  have joined := fullJoin.map (fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2))
  simp only [Functor.map_map, PqxdhDeploymentEnvironmentJoin.merge] at joined
  simpa only [CborRawNativePublic.native, CborRawEnvironmentRun.handler] using changed.trans joined.symm

/-- Startup accounting is retained from any actual fresh World state; its counted coins are never reset. -/
theorem middle_world_from (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (startupWorld : PqxdhRecordLiftWorld.State 2)
    (fresh : PqxdhDeploymentEnvironmentJoin.uncount startupWorld =
      PqxdhDeploymentEnvironmentJoin.uncount (PqxdhRecordLiftWorld.initial (n := 2)))
    (work : OracleComp Spec Result) (publicState : Public) :
    LawEq ((fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2)) <$>
        (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) work).run
          (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
      ((fun value => (value.1.1, value.1.2.1, value.2.produced, value.1.2.2.backend.2.2)) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
            (CborRawCompile.route parse))
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
              (CborRawEnvironment.environment
                (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
                  ensureInit identityIndex runtime) setup.serverKeyId)) work).run
                    (publicState, PqxdhDeploymentEnvironment.envInitial created
                      (PqxdhDeploymentIdealSteps.splitInit created)))
            (CborRecordWorldCursor.worldShell (PqxdhDeploymentEnvironmentJoin.initialized created
              startupWorld)))).run
                (PqxdhDeploymentEnvironmentJoin.initialized created startupWorld)) := by
  have exactRun := congrArg (fun program => (fun value => (value.1, value.2.1, value.2.2.base.produced, value.2.2.backend.2.2)) <$> program)
    (CborRawNativePublic.run setup wire parse checks target parameters created work
      (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq, CborRawNativePublic.reset,
    PqxdhDeploymentIdealCut.unghost] at exactRun
  refine (LawEq.of_eq exactRun.symm).trans ?_
  exact native_world_from setup wire parse checks target parameters created ensureInit identityIndex runtime
    startupWorld fresh work publicState

end Handoff
end BeaconcryptCore.Computational.CborRawWorldCoreHandoff


/-- info: 'BeaconcryptCore.Computational.CborRawWorldCoreHandoff.native_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawWorldCoreHandoff.native_world

/-- info: 'BeaconcryptCore.Computational.CborRawWorldCoreHandoff.middle_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawWorldCoreHandoff.middle_world

/-- info: 'BeaconcryptCore.Computational.CborRawWorldCoreHandoff.native_world_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawWorldCoreHandoff.native_world_from
/-- info: 'BeaconcryptCore.Computational.CborRawWorldCoreHandoff.middle_world_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawWorldCoreHandoff.middle_world_from
