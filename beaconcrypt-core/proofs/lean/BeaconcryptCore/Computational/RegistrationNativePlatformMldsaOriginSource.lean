-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource

/-! Exact restoration of the corrected source protected-origin marker retains the native state, the shared external platform state and every failed callback jointly. Only the private credential representation is mapped. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaOriginEvent (Bad)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Table" => RegistrationNativePlatformMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source
attribute [local irreducible] RegistrationNativePlatformExperiment.handler

noncomputable def handler (server : Credential source) : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT ((Native × Platform) × Bool) ProbComp) := by
  classical
  exact fun query before => (fun result => (result.1, (result.2, before.2 || decide (Bad source server query before.1.1 result.1)))) <$>
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created source server
        view failure allocation reserveRegistration reservePeer erased helper writer query) before.1

def project (fallback : Credential source) (before : Table × Bool) : (Native × Platform) × Bool :=
  ((nativeState (restore source fallback before.1.2) before.1.1.1, before.1.1.2), before.2)

variable (credential : Credential (handleSource source)) (fallback : Credential source)
local notation "tableHandler" => RegistrationNativePlatformMldsaBadSource.handler source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
local notation "original" => handler source setup checks wire route representation created view failure allocation reserveRegistration reservePeer erased helper writer fallback

/-- Each literal corrected callback restores its original protected-cut marker and the complete common platform poststate. -/
theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : Table × Bool)
    (server : Live source before.1.2 credential fallback) :
    Prod.map id (project source fallback) <$> (tableHandler query).run before = (original query).run (project source fallback before) := by
  classical
  have bare : (fun result => (result.1, (nativeState (restore source fallback result.2.2) result.2.1.1, result.2.1.2))) <$>
      (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before.1 =
      RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created source fallback view failure allocation reserveRegistration reservePeer erased helper writer query)
        (nativeState (restore source fallback before.1.2) before.1.1.1, before.1.1.2) := by
    have restored := RegistrationNativePlatformMldsaTableHandler.restored source setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer fallback before.1.2 server query before.1.1.1 before.1.1.2
    have same := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) restored
    simpa only [RegistrationNativePlatformMldsaTableCallback.callback, RegistrationNativePlatformMldsaTableCallback.arrange,
      RegistrationNativePlatformMldsaTableRestore.observe, RegistrationNativePlatformPackedState.pack, StateT.run, Functor.map_map] using same
  have event (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
      Bad source fallback query (nativeState (restore source fallback before.1.2) before.1.1.1) reply ↔
        RegistrationNativeMldsaBadCut.Bad source credential query (RegistrationNativePlatformMldsaTableStop.core source before.1) reply := by
    have same := (RegistrationNativeMldsaOriginEvent.mapped (restore source fallback before.1.2) credential query before.1.1.1 reply).trans
      (RegistrationNativeMldsaOriginEvent.table source credential query (RegistrationNativePlatformMldsaTableStop.core source before.1) reply).symm
    rw [RegistrationNativeMldsaOpaque.restore_live source fallback before.1.2 credential fallback server] at same
    exact same
  have marker (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
      decide (Bad source fallback query (nativeState (restore source fallback before.1.2) before.1.1.1) reply) =
        decide (RegistrationNativeMldsaBadCut.Bad source credential query (RegistrationNativePlatformMldsaTableStop.core source before.1) reply) := by
    simp only [event reply]
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2 ||
    decide (Bad source fallback query (nativeState (restore source fallback before.1.2) before.1.1.1) result.1)))) <$> distribution) bare
  simpa only [RegistrationNativePlatformMldsaBadSource.handler, handler, project, StateT.run, Functor.map_map, Prod.map, id_eq, marker] using same

private theorem live_step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : Table × Bool)
    (server : Live source before.1.2 credential fallback)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × (Table × Bool))
    (supported : result ∈ support ((tableHandler query).run before)) :
    Live source result.2.1.2 credential fallback := by
  simp only [RegistrationNativePlatformMldsaBadSource.handler, RegistrationNativePlatformMldsaTableCallback.callback,
    StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact RegistrationNativePlatformMldsaTableHandler.server_live source setup checks wire route representation created credential
    view failure allocation reserveRegistration reservePeer erased helper writer fallback before.1.2 server query before.1.1.1 before.1.1.2 inner reached

/-- Arbitrary adaptive typed executions preserve the original corrected source event with their common external platform state. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (before : Table × Bool)
    (server : Live source before.1.2 credential fallback) :
    Prod.map id (project source fallback) <$> (simulateQ tableHandler work).run before =
      (simulateQ original work).run (project source fallback before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      calc
        _ = (tableHandler query).run before >>= fun middle =>
            (simulateQ original (next middle.1)).run (project source fallback middle.2) := by
          apply bind_congr_of_forall_mem_support
          intro middle reached
          have nextServer := live_step source setup checks wire route representation created view failure allocation reserveRegistration reservePeer erased helper writer credential fallback query before server middle reached
          exact ih middle.1 middle.2 nextServer
        _ = (Prod.map id (project source fallback) <$> (tableHandler query).run before) >>= fun middle =>
            (simulateQ original (next middle.1)).run middle.2 := by
          rw [bind_map_left]
          rfl
        _ = _ := by rw [step source setup checks wire route representation created view failure allocation reserveRegistration reservePeer erased helper writer credential fallback query before server]

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginSource.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginSource.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginSource.program
