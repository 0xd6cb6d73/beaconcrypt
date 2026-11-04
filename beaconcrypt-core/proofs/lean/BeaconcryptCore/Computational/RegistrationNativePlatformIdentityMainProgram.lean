-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainTyped

/-! The derived generated-handle invariant composes through arbitrary adaptive current-runtime typed programs. Source interpretation retains every reply, ledger-independent native effect and complete shared P poststate; no whole-game equality or invariant-preservation premise is supplied by callers. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open RegistrationNativePlatformIdentityMainOwned (Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "handler" => RegistrationNativePlatformIdentityMainTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "target" => RegistrationNativePlatformIdentityMainTyped.target setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

omit primitives in
/-- The literal private source interpreter distributes over every adaptive executable query tree. -/
theorem interpret_program {κ : Type} {spec : OracleSpec κ}
    (joint : PqxdhJointIdentity.Primitives) (client : QueryImpl spec (M n KemSK Platform source)) (work : OracleComp spec Value) :
    interpret joint (simulateQ client work) = simulateQ (fun query => interpret joint (client query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using RegistrationNativePlatformIdentityMainOrdinary.interpret_pure joint value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityMainOrdinary.interpret_bind]
    apply congrArg (fun continuation => interpret joint (client query) >>= continuation)
    funext reply
    exact ih reply

noncomputable def compiled : QueryImpl TypedSpec (StateT ((State n KemSK source × Platform) × SourceState) ProbComp) :=
  fun query => interpret setup.joint (handler query)

/-- Every reached callback prefix retains actual generated-row ownership from initialization. -/
theorem program_owned (work : OracleComp TypedSpec Value) (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (simulateQ handler work)).run before)) :
    Owned setup.joint result.2 := by
  rw [interpret_program] at reached
  exact simulateQ_run_preservesInv
    (compiled setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (Owned setup.joint)
    (fun query current prior after supported => RegistrationNativePlatformIdentityMainTyped.handler_owned
      setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current after prior supported)
    work before owned result reached

/-- Complete adaptive source execution recovers the literal chosen native runtime and full platform state, with the reachable invariant discharged internally at every callback. -/
theorem program_source (work : OracleComp TypedSpec Value) (before : (State n KemSK source × Platform) × SourceState)
    (owned : Owned setup.joint before) :
    Prod.map id project <$> (interpret setup.joint (simulateQ handler work)).run before =
      (simulateQ target work).run (project before) := by
  rw [interpret_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiled setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    target (Owned setup.joint) project
    (fun query current prior after supported => RegistrationNativePlatformIdentityMainTyped.handler_owned
      setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current after prior supported)
    (fun query current prior => RegistrationNativePlatformIdentityMainTyped.query_source
      setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current prior)
    work before owned

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram.interpret_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram.interpret_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram.program_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram.program_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProgram.program_source
