-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
import BeaconcryptCore.Computational.RegistrationNativeMldsaBadSource

/-! The actual protected-origin marker transports from the reached private key-table execution to the literal original native source, retaining its complete native poststate and marker jointly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaOriginEvent (Bad)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Table" => RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) source
attribute [local irreducible] RegistrationNativeExperiment.handler

noncomputable def handler (server : Credential source) : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (Native × Bool) ProbComp) := by
  classical
  exact fun query before => (fun result => (result.1, (result.2, before.2 || decide (Bad source server query before.1 result.1)))) <$>
    (RegistrationNativeExperiment.handler setup checks wire route representation created source server query).run before.1

def project (fallback : Credential source) (before : Table × Bool) : Native × Bool :=
  (nativeState (restore source fallback before.1.2) before.1.1, before.2)

variable (credential : Credential (handleSource source)) (fallback : Credential source)
local notation "tableHandler" => RegistrationNativeMldsaBadSource.handler source setup checks wire route representation created credential
local notation "original" => handler source setup checks wire route representation created fallback

/-- One actual complete callback transports its original bad-cut marker, with its actual private-key restoration. -/
theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : Table × Bool)
    (server : Live source before.1.2 credential fallback) :
    Prod.map id (project source fallback) <$> (tableHandler query).run before = (original query).run (project source fallback before) := by
  classical
  have bare : (fun result => (result.1, nativeState (restore source fallback result.2.2) result.2.1)) <$>
      (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential query).run before.1 =
      (RegistrationNativeExperiment.handler setup checks wire route representation created source fallback query).run
        (nativeState (restore source fallback before.1.2) before.1.1) := by
    simp only [RegistrationNativeMldsaTableStop.callback, StateT.run, Functor.map_map]
    exact RegistrationNativeMldsaTableHandler.restored source setup checks wire route representation created credential fallback before.1.2 server query before.1.1
  have event (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
      Bad source fallback query (nativeState (restore source fallback before.1.2) before.1.1) reply ↔
        RegistrationNativeMldsaBadCut.Bad source credential query before.1 reply := by
    have same := (RegistrationNativeMldsaOriginEvent.mapped (restore source fallback before.1.2) credential query before.1.1 reply).trans
      (RegistrationNativeMldsaOriginEvent.table source credential query before.1 reply).symm
    rw [RegistrationNativeMldsaOpaque.restore_live source fallback before.1.2 credential fallback server] at same
    exact same
  have marker (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
      decide (Bad source fallback query (nativeState (restore source fallback before.1.2) before.1.1) reply) =
        decide (RegistrationNativeMldsaBadCut.Bad source credential query before.1 reply) := by
    simp only [event reply]
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2 ||
    decide (Bad source fallback query (nativeState (restore source fallback before.1.2) before.1.1) result.1)))) <$> distribution) bare
  simpa only [RegistrationNativeMldsaBadSource.handler, handler, project, StateT.run, Functor.map_map, Prod.map, id_eq, marker] using same

private theorem live_step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : Table × Bool)
    (server : Live source before.1.2 credential fallback)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × (Table × Bool))
    (supported : result ∈ support ((tableHandler query).run before)) :
    Live source result.2.1.2 credential fallback := by
  simp only [RegistrationNativeMldsaBadSource.handler, RegistrationNativeMldsaTableStop.callback,
    StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaTableHandler.server_live source setup checks wire route representation created credential fallback
    before.1.2 server query before.1.1 inner reached

/-- Every adaptive typed source execution preserves the exact original native marker through the dynamic actual table. -/
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
          have nextServer := live_step source setup checks wire route representation created credential fallback query before server middle reached
          exact ih middle.1 middle.2 nextServer
        _ = (Prod.map id (project source fallback) <$> (tableHandler query).run before) >>= fun middle =>
            (simulateQ original (next middle.1)).run middle.2 := by
          rw [bind_map_left]
          rfl
        _ = _ := by rw [step source setup checks wire route representation created credential fallback query before server]

end BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSource.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSource.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginSource.program
