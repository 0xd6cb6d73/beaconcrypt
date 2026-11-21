-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleSimulation
import BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-! Public raw-CBOR registration adaptation is an environment transformer. The environment retains only creation pins, registration replies and the assigned-ID counter beside its existing private state. It delegates once, including oversized moved-token builds, and keeps the original optional outer writer. Record commands and secrecy draws remain outside this restricted registration environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawEnvironment
open PqxdhRecordLiftInterface (Environment EnvQuery EnvSpec EnvEffects EffectKind effectKind)
open PqxdhDeploymentInterface (Spec)
open CborRawPublicState (Public toMemory)
variable {n : Nat} {E : Type}

/-- Choose the source registration request using only the public state. -/
def request (state : Public) (query : EnvQuery) : EnvQuery := by
  rcases query with ⟨command, valid⟩
  cases command
  case build session payload =>
    exact ⟨.build session (CborAdmissionCompiler.buildPayload state.lastId payload), trivial⟩
  case finish owner raw =>
    exact ⟨.finish owner (CborTaggedCodec.tag (CborPublicPin.pin (toMemory state) owner) raw), trivial⟩
  all_goals exact ⟨_, valid⟩

theorem request_spec (state : Public) (query : EnvQuery) :
    .inr (request state query).val = CborRawMiddleRegistration.request (toMemory state) (.inr query.val) := by
  rcases query with ⟨command, valid⟩
  cases command <;> rfl

/-- Only a returned build envelope is stripped; failure stays failure. -/
def reply (state : Public) (query : EnvQuery) : EnvSpec.Range (request state query) → EnvSpec.Range query := by
  rcases query with ⟨command, valid⟩
  cases command
  case build => exact Option.map CborPublicClient.strip
  all_goals exact id

/-- Retain the delegated reply in the public registration log before exposing its raw representation. -/
def next (state : Public) (query : EnvQuery) (value : EnvSpec.Range (request state query)) : Public := by
  refine ⟨CborRegistrationPublicLog.update state.log (.inr (request state query).val) value, ?_⟩
  rcases query with ⟨command, valid⟩
  cases command
  case build => exact (value.map PqxdhServerRegistrationPublication.Response.keyId).getD state.lastId
  all_goals exact state.lastId

/-- The public adapter introduces no effect and cannot read a record kernel, the shared cache or a secret ledger. -/
noncomputable def step (env : Environment n E) (query : EnvQuery) :
    StateT (Public × E) (OracleComp (EnvEffects n)) (EnvSpec.Range query) := fun state =>
  (fun value => (reply state.1 query value.1, (next state.1 query value.1, value.2))) <$>
    (env.step (request state.1 query)).run state.2

noncomputable def environment (env : Environment n E) (serverKeyId : Std.U64) : Environment n (Public × E) where
  start := (Option.map fun value => (value.1, (⟨PqxdhDeploymentCompile.Log.empty, serverKeyId⟩, value.2))) <$> env.start
  step := step env

theorem step_run (env : Environment n E) (query : EnvQuery) (state : Public × E) :
    (step env query).run state =
      (fun value => (reply state.1 query value.1, (next state.1 query value.1, value.2))) <$>
        (env.step (request state.1 query)).run state.2 := rfl

/-- Every public request retains its original command class, including oversized builds. -/
theorem request_class (state : Public) (query : EnvQuery) :
    PqxdhDeploymentInterface.queryClass (.inl (.inr (request state query).val)) =
      PqxdhDeploymentInterface.queryClass (.inl (.inr query.val)) := by
  rcases query with ⟨command, valid⟩
  cases command <;> simp only [request, PqxdhDeploymentInterface.queryClass]

/-- The exact all-reply resource frame is preserved. Neither public adaptation nor failure normalization spends a coin, hash or administrative capability. -/
theorem frame (env : Environment n E) (serverKeyId : Std.U64) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat)
    (bounded : PqxdhRecordLiftInterface.Frame env startup allowance) :
    PqxdhRecordLiftInterface.Frame (environment env serverKeyId) startup allowance := by
  refine ⟨?_, ?_⟩
  · simpa only [environment, IsTotalQueryBound, isQueryBound_map_iff] using bounded.1
  · intro query state kind
    rw [show ((environment env serverKeyId).step query).run state = _ from step_run env query state]
    apply (OracleComp.isQueryBoundP_map_iff _ _ _).mpr
    simpa only [request_class] using bounded.2 (request state.1 query) state.2 kind

end BeaconcryptCore.Computational.CborRawEnvironment

/-- info: 'BeaconcryptCore.Computational.CborRawEnvironment.request_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironment.request_spec

/-- info: 'BeaconcryptCore.Computational.CborRawEnvironment.step_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironment.step_run

/-- info: 'BeaconcryptCore.Computational.CborRawEnvironment.request_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironment.request_class

/-- info: 'BeaconcryptCore.Computational.CborRawEnvironment.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironment.frame
