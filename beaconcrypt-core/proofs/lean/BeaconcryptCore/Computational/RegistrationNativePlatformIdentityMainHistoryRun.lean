-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainFull
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun

/-! The derived generated-handle invariant composes through arbitrary adaptive current-runtime typed programs. Source interpretation retains every reply, ledger-independent native effect and complete shared P poststate; no whole-game equality or invariant-preservation premise is supplied by callers. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open RegistrationNativePlatformIdentityMainHistory (Inv)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
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

private theorem ambient_inv (query : TypedSpec.Domain) (before : (State n KemSK source × Platform) × SourceState)
    (result : TypedSpec.Range query × ((State n KemSK source × Platform) × SourceState))
    (prior : Inv setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMainAmbient.step setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)).run before)) : Inv setup.joint result.2 := by
  apply RegistrationNativePlatformIdentityMainHistory.ordinary_inv setup.joint _ before result prior
  exact reached

attribute [local irreducible] RegistrationNativePlatformIdentityMainAmbient.step RegistrationNativePlatformIdentityMainAmbient.command

/-- Every actual source callback preserves genuine generated-row ownership on all failed and successful paths. -/
theorem handler_inv (query : TypedSpec.Domain) (before : (State n KemSK source × Platform) × SourceState)
    (result : TypedSpec.Range query × ((State n KemSK source × Platform) × SourceState))
    (prior : Inv setup.joint before)
    (reached : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityMainTyped.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)).run before)) :
    Inv setup.joint result.2 := by
  cases query with
  | inl coin => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin) before result prior reached
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityMainHistory.create_inv setup checks representation created edPin mlPin keyId before result prior reached
    | bundle index => exact RegistrationNativePlatformIdentityMainHistory.bundle_inv setup checks representation created writer index before result prior reached
    | finish index packet => exact RegistrationNativePlatformIdentityMainHistory.finish_inv setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet before result prior reached
    | accept packet =>
      unfold RegistrationNativePlatformIdentityMainTyped.handler at reached
      rw [RegistrationNativePlatformIdentityMainOrdinary.interpret_bind, StateT.run_bind,
        RegistrationNativePlatformIdentityMainOrdinary.report_source, pure_bind] at reached
      exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)) before result prior reached
    | build session application => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build session application)) before result prior reached
    | hmac key message => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hmac key message)) before result prior reached
    | hash bytes => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes)) before result prior reached
    | serverSend keyId plaintext => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext)) before result prior reached
    | serverRaw raw => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw)) before result prior reached
    | beaconSend index plaintext => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext)) before result prior reached
    | beaconRaw index raw => exact ambient_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw)) before result prior reached


/-- Every reached adaptive current-runtime prefix retains exact generated signing histories. -/
theorem program_inv (work : OracleComp TypedSpec Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint (simulateQ handler work)).run before)) :
    Inv setup.joint result.2 := by
  rw [RegistrationNativePlatformIdentityMainProgram.interpret_program] at supported
  exact simulateQ_run_preservesInv
    (RegistrationNativePlatformIdentityMainProgram.compiled setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (Inv setup.joint)
    (fun query current previous next reached => handler_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current next previous reached)
    work before prior result supported

/-- The complete original raw/secrecy compiler preserves the same full native/platform signing-history invariant. -/
theorem run_inv (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : (Value × RegistrationNativeLedger.State) × ((State n KemSK source × Platform) × SourceState))
    (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work)).run before)) :
    Inv setup.joint result.2 :=
  program_inv setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result prior supported

omit primitives in
/-- Empty current owner initialization establishes all internal chronological signing-history obligations. -/
theorem initial_inv (joint : PqxdhJointIdentity.Primitives) (context : RegistrationNativeIdentityWorld.Context n KemSK) (previous : Platform) :
    Inv (source := source) joint ((⟨context,[]⟩,previous),PqxdhDynamicIdentityPool.initialState) :=
  RegistrationNativeIdentityMainHistoryRun.initial_inv joint context

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.handler_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.handler_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.program_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.program_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.run_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.run_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.initial_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun.initial_inv
