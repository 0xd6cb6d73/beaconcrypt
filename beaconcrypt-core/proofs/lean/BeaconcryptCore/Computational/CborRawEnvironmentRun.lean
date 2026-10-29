-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawGuardedJoin
import BeaconcryptCore.Computational.CborRawPublicClient

/-! A complete raw registration environment and its native split execution have the same adaptive run. Public adaptation is below the original secrecy program; the actual World cursor filter is below both. The fixed-parameter ideal startup discharges admissibility and its private invariant from the existing concrete initial states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawEnvironmentRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good Splits Stable)
open PqxdhDeploymentBackend (RegImpl XState)
open CborRawPublicState (Public)
open CborRecordWorldCursor (worldShell)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response Bk E Result : Type} {baseSpec : OracleSpec ι} {n : Nat}

/-- The actual cursor compiler commutes with pure output mapping and spends no additional query. -/
theorem cursor_map {Input Output : Type} (f : Input → Output) (work : OracleComp (WorldSpec n) Input)
    (shell : CborRecordWorldClient.Shell) :
    CborRecordWorldClient.client (f <$> work) shell = f <$> CborRecordWorldClient.client work shell := by
  simp only [CborRecordWorldClient.client, simulateQ_map, StateT.run_map, Functor.map_map]

/-- The guarded native interpreter with public registration bookkeeping as its only auxiliary state. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (reg : RegImpl KemSK Bk n) :
    QueryImpl Spec (StateT (Public × XState KemSK Bk n) ProbComp) :=
  ((CborRawGuardedJoin.nativeHandler setup codec route reg).mapStateTBase CborRawPublicClient.handler).flattenStateT

theorem handler_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (reg : RegImpl KemSK Bk n)
    (query : Spec.Domain) (state : Public × XState KemSK Bk n) :
    (handler setup codec route reg query).run state =
      (fun value => (CborRawPublicClient.reply state.1 query value.1,
        (CborRawPublicClient.next state.1 query value.1, value.2))) <$>
        (CborRawGuardedJoin.nativeHandler setup codec route reg
          (CborRawPublicClient.request state.1 query)).run state.2 := by
  rw [handler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  have localStep : (CborRawPublicClient.handler query).run state.1 =
      (fun value => (CborRawPublicClient.reply state.1 query value,
        CborRawPublicClient.next state.1 query value)) <$>
        (Spec.query (CborRawPublicClient.request state.1 query) : OracleComp Spec _) := by
    exact bind_pure_comp _ _
  rw [localStep, simulateQ_map, StateT.run_map, simulateQ_spec_query, Functor.map_map]

/-- Full raw environment and native split runs have the same law, including all private state and public raw replies. -/
theorem run_join (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n (EnvState KemSK Bk)) (serverKeyId : Std.U64)
    (reg : RegImpl KemSK Bk n) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv) (work : OracleComp Spec Result)
    (state : Public × EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n)
    (good : Good created state.2 world) (holds : inv state.2 world) :
    LawEq ((fun value => (value.1.1, (value.1.2.1,
          PqxdhDeploymentEnvironmentJoin.merge value.1.2.2 value.2))) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
          (CborRecordWorldClient.client
            ((simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment env serverKeyId)) work).run state)
            (worldShell world))).run world)
      ((simulateQ (handler setup codec route reg) work).run
        (state.1, PqxdhDeploymentEnvironmentJoin.merge state.2 world)) := by
  have joined := CborRawGuardedJoin.run_join setup codec route env reg created inv stable splits
    (CborRawPublicClient.client work state.1) state.2 world good holds
  rw [CborRawPublicClient.native_program env serverKeyId work state, cursor_map, simulateQ_map, StateT.run_map,
    Functor.map_map] at joined
  have result := joined.map (fun value => (value.1.1, (value.1.2, value.2)))
  rw [CborRawPublicClient.client, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    Functor.map_map, Functor.map_map] at result
  simpa only [handler, Prod.eta, id_map'] using result

section Ideal
open PqxdhDeploymentIdealParams (Target Params)
variable {A : Type} (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)

/-- Actual ideal registration instance with independent native record codec and source registration codec. -/
theorem ideal_run_join (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result)
    (state : Public × EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (good : Good created state.2 world)
    (holds : PqxdhDeploymentIdealEnv.IdealInv target state.2 world) :
    LawEq ((fun value => (value.1.1, (value.1.2.1,
          PqxdhDeploymentEnvironmentJoin.merge value.1.2.2 value.2))) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
            (CborRawCompile.route parse))
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
              (CborRawEnvironment.environment
                (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
                  ensureInit identityIndex runtime) setup.serverKeyId)) work).run state)
            (worldShell world))).run world)
      ((simulateQ (handler setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse)
          (PqxdhDeploymentIdealDefer.idealSplit setup (CborRawCompile.sourceCodec wire parse)
            (CborRawCompile.route parse) checks target parameters created)) work).run
        (state.1, PqxdhDeploymentEnvironmentJoin.merge state.2 world)) :=
  run_join setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse) _ _ _ created
    (PqxdhDeploymentIdealEnv.IdealInv target) (PqxdhDeploymentIdealEnv.idealInv_stable target)
    (PqxdhDeploymentIdealEnv.ideal_splits setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
      checks target parameters created) work state world good holds

/-- Startup supplies the ideal invariant and native reassembly, with no caller-supplied cursor or private-state invariant. -/
theorem ideal_initialized (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result) (publicState : Public) :
    LawEq ((fun value => (value.1.1, (value.1.2.1,
          PqxdhDeploymentEnvironmentJoin.merge value.1.2.2 value.2))) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
            (CborRawCompile.route parse))
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
              (CborRawEnvironment.environment
                (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
                  ensureInit identityIndex runtime) setup.serverKeyId)) work).run
                    (publicState, PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created)))
            (worldShell (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := 2)))))).run
          (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := 2))))
      ((simulateQ (handler setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse)
          (PqxdhDeploymentIdealDefer.idealSplit setup (CborRawCompile.sourceCodec wire parse)
            (CborRawCompile.route parse) checks target parameters created)) work).run
        (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))) := by
  have joined := ideal_run_join setup wire parse checks target parameters ensureInit identityIndex runtime created work
    (publicState, PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created))
    (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := 2)))
    (PqxdhDeploymentEnvironmentJoin.good_initial created (PqxdhDeploymentIdealSteps.splitInit created) _ rfl)
    (PqxdhDeploymentIdealEnv.idealInv_start target created)
  rw [PqxdhDeploymentEnvironmentJoin.merge_initial created (PqxdhDeploymentIdealSteps.splitInit created) _ rfl] at joined
  exact joined

end Ideal
end BeaconcryptCore.Computational.CborRawEnvironmentRun

/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentRun.cursor_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentRun.cursor_map
/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentRun.run_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentRun.run_join
/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentRun.ideal_run_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentRun.ideal_run_join
/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentRun.ideal_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentRun.ideal_initialized

/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentRun.handler_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentRun.handler_run
