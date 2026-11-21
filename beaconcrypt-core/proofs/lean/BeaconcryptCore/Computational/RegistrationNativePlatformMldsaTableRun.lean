-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler

/-! Dynamic ML table restoration commutes with every adaptive corrected platform execution. The actual reached key table, Native state and public platform state are threaded at each callback, while the unchanged compiler retains its original ledger and test bit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformMldsaTableRestore (observe)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source)) (fallback : Credential source)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformMldsaProfile.handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
local notation "original" => RegistrationNativePlatformExperiment.handler (n := n) RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created source fallback view failure allocation reserveRegistration reservePeer erased helper writer

/-- Arbitrary adaptive source programs restore exactly at their actual final table, with every native and public platform poststate retained. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) (pool : Pool source)
    (server : Live source pool credential fallback) :
    observe source fallback <$> runState source (simulateQ callback work) before previous pool =
      (((simulateQ original work).run (nativeState (restore source fallback pool) before)).run previous) := by
  induction work using OracleComp.inductionOn generalizing before previous pool with
  | pure value =>
    simp only [simulateQ_pure, RegistrationNativePlatformMldsaTableProgram.run_pure, map_pure, StateT.run_pure]
    rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformMldsaTableProgram.run_bind,
      map_bind, StateT.run_bind]
    calc
      _ = runState source (callback query) before previous pool >>= fun middle =>
          (((simulateQ original (next middle.1.1.1)).run
            (nativeState (restore source fallback middle.2) middle.1.1.2)).run middle.1.2) := by
        apply bind_congr_of_forall_mem_support
        intro middle reached
        exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2
          (RegistrationNativePlatformMldsaTableHandler.server_live source setup checks wire route representation created credential
            view failure allocation reserveRegistration reservePeer erased helper writer fallback pool server query before previous middle reached)
      _ = (observe source fallback <$> runState source (callback query) before previous pool) >>= fun middle =>
          (((simulateQ original (next middle.1.1)).run middle.1.2).run middle.2) := by
        rw [bind_map_left]
        rfl
      _ = _ := by
        rw [RegistrationNativePlatformMldsaTableHandler.restored source setup checks wire route representation created credential
          view failure allocation reserveRegistration reservePeer erased helper writer fallback pool server query before previous]

/-- The complete unchanged raw/secrecy compiler preserves its literal ledger and test bit under actual corrected platform restoration. -/
theorem run (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) (pool : Pool source)
    (server : Live source pool credential fallback) :
    observe source fallback <$>
      RegistrationNativeMldsaTableProgram.evaluate source
        ((RegistrationNativePlatformMldsaProfile.run setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer erased helper writer bounds mode work before).run previous) pool =
      ((RegistrationNativePlatformExperiment.run RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created source fallback
        view failure allocation reserveRegistration reservePeer erased helper writer bounds mode work
          (nativeState (restore source fallback pool) before)).run previous) :=
  program source setup checks wire route representation created credential fallback view failure allocation reserveRegistration reservePeer erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before previous pool server
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun.run
