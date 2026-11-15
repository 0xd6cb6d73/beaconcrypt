-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCreation
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer

/-! The complete original native profile is an exact interpretation of an additive ML capability program. Actual startup, original bit/fresh ledger, native raw adapter, all controller failures and complete shared cache/signing history are retained. Primitive-oracle substitutions may act at named generate/sign leaves; this evaluator theorem does not assume authentication or equate distinct primitive games. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaProfile
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaProgram (Spec liftState evalState evaluate)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeInterface (ModeSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def server (work : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) Value) :
    StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)) Value := fun before =>
  (fun result => (result.1, { before with server := result.2 })) <$> work.run before.server

/-- The original source Server lens retains its complete current native envelope under evaluation. -/
theorem eval_server (work : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) Value) :
    evalState (server (KemSK := KemSK) work) = RegistrationNativeExperiment.server (evalState work) := by
  funext before
  simp only [server, evalState, evaluate, RegistrationNativeExperiment.server, StateT.run, simulateQ_map]

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)))
  | .inr (.create edPin mlPin keyId) =>
      RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId
  | .inr (.bundle owner) => RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created owner
  | .inr (.build session application) => server
      (RegistrationNativeMldsaServer.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
        checks wire.encodeResponse session application)
  | query => liftState (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)

/-- Every original typed callback, including all mandatory checks and private record operations, is recovered by actual ML evaluation. -/
theorem eval_handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    evalState (handler (n := n) setup checks wire route representation created credential query) =
      RegistrationNativeExperiment.handler setup checks wire route representation created source credential query := by
  cases query with
  | inl coin => exact RegistrationNativeMldsaProgram.eval_liftState _
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativeMldsaCreation.eval_create setup checks representation created edPin mlPin keyId
    | bundle owner => exact RegistrationNativeMldsaBundle.eval_sourceBundle setup checks wire representation created owner
    | build session application =>
        rw [handler, eval_server, RegistrationNativeMldsaServer.eval_build]
        rfl
    | _ => exact RegistrationNativeMldsaProgram.eval_liftState _

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value) (before : RegistrationNativeExperiment.State n KemSK source) :
    OracleComp (Spec source) (Value × (RegistrationNativeLedger.State × RegistrationNativeExperiment.State n KemSK source)) :=
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (handler setup checks wire route representation created credential)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).run before

/-- Whole original native execution is restored under the unchanged raw adapter and literal original secrecy ledger. -/
theorem eval_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value) (before : RegistrationNativeExperiment.State n KemSK source) :
    evaluate (run setup checks wire route representation created credential bounds mode work before) =
      RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before := by
  have law := RegistrationNativeMldsaProgram.eval_simulate
    (handler (n := n) setup checks wire route representation created credential)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
  have callbacks : (fun query => evalState (handler (n := n) setup checks wire route representation created credential query)) =
      RegistrationNativeExperiment.handler setup checks wire route representation created source credential :=
    funext (eval_handler setup checks wire route representation created credential)
  rw [callbacks] at law
  have atState := congrFun law before
  simp only [evalState, evaluate, StateT.run] at atState
  simp only [run, evaluate, simulateQ_map, RegistrationNativeExperiment.run,
    RegistrationNativeFullCompiler.compile_run, StateT.run]
  rw [atState]

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    OracleComp (Spec source) Bool := do
  let initialized ← RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure false
  | some initial =>
      event <$> run setup checks wire route representation initial.created initial.credential
        bounds mode (adversary initial.public) initial.state

/-- Actual interpretation recovers the complete original native profile, from effectful startup through its literal final event. -/
theorem eval_profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    evaluate (profile setup checks wire route representation ensureInit identityIndex serverKeyId bounds mode adversary event) =
      RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode adversary event := by
  unfold profile RegistrationNativeExperiment.profile
  simp only [evaluate, simulateQ_bind]
  rw [← evaluate, RegistrationNativeMldsaCreation.eval_start]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => simp only [simulateQ_pure]
  | some initial =>
      simp only [simulateQ_map]
      rw [← evaluate, eval_run]

end BeaconcryptCore.Computational.RegistrationNativeMldsaProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProfile.eval_profile
