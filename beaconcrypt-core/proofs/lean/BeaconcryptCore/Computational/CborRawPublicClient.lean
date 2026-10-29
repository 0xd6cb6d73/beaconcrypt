-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawEnvironment

/-! The public registration transformation as an open CE client. Running it below the original secrecy wrapper retains that wrapper's raw transcript and secret sampling order. This form reuses simulations for arbitrary CE programs, with no copied kernel or hidden field read. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPublicClient
open PqxdhDeploymentInterface (Spec)
open PqxdhRecordLiftInterface (Environment WorldSpec)
open CborRawPublicState (Public toMemory)
variable {n : Nat} {E Result : Type}

def request (state : Public) (query : Spec.Domain) : Spec.Domain :=
  CborRawMiddleRegistration.request (toMemory state) query

def reply (state : Public) (query : Spec.Domain) : Spec.Range (request state query) → Spec.Range query :=
  CborRawMiddleRegistration.reply (toMemory state) query

def next (state : Public) (query : Spec.Domain) (value : Spec.Range (request state query)) : Public :=
  ⟨CborRegistrationPublicLog.update state.log (request state query) value,
    CborRawMiddleRegistration.assignment (toMemory state) query value⟩

/-- Delegate once, then retain the actual optional public reply before exposing its native representation. -/
noncomputable def handler : QueryImpl Spec (StateT Public (OracleComp Spec)) := fun query state => do
  let value ← (Spec.query (request state query) : OracleComp Spec _)
  pure (reply state query value, next state query value)

noncomputable def client (work : OracleComp Spec Result) (initial : Public) :
    OracleComp Spec (Result × Public) := (simulateQ handler work).run initial

/-- A pure public reply cannot turn failure into success. -/
theorem build_reply (state : Public) (session : Nat) (payload : Option Pqxdh.Bytes) :
    reply state (.inr (.build session payload)) none = none := rfl

/-- All record operations retain the complete public registration state. -/
theorem record_next (state : Public) (query : Spec.Domain)
    (record : CborSplitCompiler.recordCommand query = true) (value : Spec.Range (request state query)) :
    next state query value = state := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command
    case serverSend => cases state; rfl
    case serverRaw => cases state; rfl
    case beaconSend => cases state; rfl
    case beaconRaw => cases state; rfl
    all_goals simp [CborSplitCompiler.recordCommand] at record

/-- The public client's query class is unchanged; only build admission and the finish envelope are normalized. -/
theorem request_class (state : Public) (query : Spec.Domain) :
    PqxdhDeploymentInterface.queryClass (.inl (request state query)) =
      PqxdhDeploymentInterface.queryClass (.inl query) := by
  rcases query with coin | command
  · rfl
  · cases command <;> simp only [request, CborRawMiddleRegistration.request,
      PqxdhDeploymentInterface.queryClass]

private theorem map_state_apply {Input Output : Type} (f : Input → Output)
    (work : StateT E (OracleComp (WorldSpec n)) Input) (state : E) :
    (f <$> work) state = Prod.map f id <$> work state :=
  bind_pure_comp (Prod.map f id) (work state)

/-- Environment registration adaptation and the public CE client have the same open query semantics, including private environment output. -/
theorem native_step (env : Environment n E) (serverKeyId : Std.U64) (query : Spec.Domain)
    (state : Public × E) :
    (fun value => (value.1.1, (value.1.2, value.2))) <$>
        (simulateQ (PqxdhRecordLiftInterface.native env) ((handler query).run state.1)).run state.2 =
      (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment env serverKeyId) query).run state := by
  rcases query with coin | command
  · simp only [handler, request, reply, next, CborRawMiddleRegistration.request, CborRawMiddleRegistration.reply, CborRawMiddleRegistration.assignment, StateT.run, simulateQ_map, simulateQ_spec_query,
      PqxdhRecordLiftInterface.native, bind_pure_comp]
    rfl
  · cases command
    all_goals
      simp only [handler, request, reply, next, CborRawMiddleRegistration.request, CborRawMiddleRegistration.reply, CborRawMiddleRegistration.assignment, CborRawEnvironment.request, CborRawEnvironment.reply, CborRawEnvironment.next, StateT.run, simulateQ_map, simulateQ_spec_query, bind_pure_comp, PqxdhRecordLiftInterface.native, PqxdhRecordLiftInterface.environmentStep,
        CborRawEnvironment.environment, CborRawEnvironment.step]
      first
      | rfl
      | erw [map_state_apply]
        dsimp only [PqxdhRecordLiftInterface.environmentStep, StateT.run]
        erw [Functor.map_map]
        rfl

/-- Flattening the public client and original environment is exactly the transformed environment, on every query and complete state. -/
theorem native_handler (env : Environment n E) (serverKeyId : Std.U64) :
    ((PqxdhRecordLiftInterface.native env).mapStateTBase handler).flattenStateT =
      PqxdhRecordLiftInterface.native (CborRawEnvironment.environment env serverKeyId) := by
  funext query
  apply StateT.ext
  intro state
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  exact native_step env serverKeyId query state

/-- The entire adaptive public client and original environment equal the raw transformed environment. This retains full private outputs and may be placed below the unchanged secrecy wrapper. -/
theorem native_program (env : Environment n E) (serverKeyId : Std.U64) (work : OracleComp Spec Result)
    (state : Public × E) :
    (simulateQ (PqxdhRecordLiftInterface.native env) (client work state.1)).run state.2 =
      (fun value => ((value.1, value.2.1), value.2.2)) <$>
        (simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment env serverKeyId)) work).run state := by
  rw [client, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, native_handler]

end BeaconcryptCore.Computational.CborRawPublicClient

/-- info: 'BeaconcryptCore.Computational.CborRawPublicClient.build_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicClient.build_reply
/-- info: 'BeaconcryptCore.Computational.CborRawPublicClient.record_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicClient.record_next
/-- info: 'BeaconcryptCore.Computational.CborRawPublicClient.request_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicClient.request_class
/-- info: 'BeaconcryptCore.Computational.CborRawPublicClient.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicClient.native_step

/-- info: 'BeaconcryptCore.Computational.CborRawPublicClient.native_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicClient.native_handler
/-- info: 'BeaconcryptCore.Computational.CborRawPublicClient.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicClient.native_program
