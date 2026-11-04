-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableHandler

/-! Dynamic private ML table interpretation commutes with arbitrary adaptive typed native execution. The invariant is derived callback by callback and preserves the real Server credential, all owner handles, original native state and source draw counts. The original record ledger remains inside the compiled program without a substituted test bit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaPoolMap (StateLive)
open RegistrationNativeMldsaTableProgram (evaluate runState)
open RegistrationNativeMldsaTableRestore (observe)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeInterface (ModeSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : Credential (handleSource source)) (fallback : Credential source)
local notation "callback" => RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential
local notation "original" => RegistrationNativeExperiment.handler setup checks wire route representation created source fallback
attribute [local irreducible] RegistrationNativeExperiment.handler

/-- Arbitrary adaptive native programs restore through their actual final private table, with no source-correspondence or ownership conclusion premise. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (server : Live source pool credential fallback) (owners : StateLive source pool before) :
    observe source fallback <$> runState source (simulateQ callback work) before pool =
      (simulateQ original work).run (nativeState (restore source fallback pool) before) := by
  induction work using OracleComp.inductionOn generalizing before pool with
  | pure value =>
      simp only [simulateQ_pure, RegistrationNativeMldsaTableProgram.run_pure, map_pure, StateT.run_pure]
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeMldsaTableProgram.run_bind,
        map_bind, StateT.run_bind]
      calc
        _ = runState source (callback query) before pool >>= fun middle =>
            (simulateQ original (next middle.1.1)).run (nativeState (restore source fallback middle.2) middle.1.2) := by
          apply bind_congr_of_forall_mem_support
          intro middle reached
          exact ih middle.1.1 middle.1.2 middle.2
            (RegistrationNativeMldsaTableHandler.server_live source setup checks wire route representation created
              credential fallback pool server query before owners middle reached)
            (RegistrationNativeMldsaTableHandler.live source setup checks wire route representation created
              credential fallback pool server query before owners middle reached)
        _ = (observe source fallback <$> runState source (callback query) before pool) >>= fun middle =>
            (simulateQ original (next middle.1)).run middle.2 := by
          rw [bind_map_left]
          rfl
        _ = _ := by rw [RegistrationNativeMldsaTableHandler.restored source setup checks wire route representation created
          credential fallback pool server query before owners]

def observeRun (fallback : Credential source)
    (result : (Value × (RegistrationNativeLedger.State × RegistrationNativeExperiment.State n KemSK (handleSource source))) × Pool source) :
    Value × (RegistrationNativeLedger.State × RegistrationNativeExperiment.State n KemSK source) :=
  (result.1.1, (result.1.2.1, nativeState (restore source fallback result.2) result.1.2.2))

private theorem evaluate_map {Answer Result : Type} (observer : Answer → Result)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Answer) (pool : Pool source) :
    evaluate source (observer <$> work) pool = Prod.map observer id <$> evaluate source work pool := by
  simp only [evaluate, simulateQ_map, StateT.run_map]
  rfl

/-- The actual complete compiled native run restores the original ledger, public outcome, test bit and native state together. -/
theorem run (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (server : Live source pool credential fallback) (owners : StateLive source pool before) :
    observeRun source fallback <$>
      evaluate source (RegistrationNativeMldsaProfile.run setup checks wire route representation created credential bounds mode work before) pool =
      RegistrationNativeExperiment.run setup checks wire route representation created source fallback bounds mode work
        (nativeState (restore source fallback pool) before) := by
  have main := program source setup checks wire route representation created credential fallback
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
    before pool server owners
  have projected := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> action) main
  simp only [RegistrationNativeMldsaProfile.run, evaluate_map, Functor.map_map, observeRun,
    observe, RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run, StateT.run] at projected ⊢
  exact projected
end BeaconcryptCore.Computational.RegistrationNativeMldsaTableRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableRun.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableRun.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableRun.run
