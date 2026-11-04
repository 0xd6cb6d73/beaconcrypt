-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds
/-! The actual original FullCompiler command bounds instantiate the literal shared-CTX typed Ed bills in every original mode. The full result, ledger, test bit, fresh-event state, failure branches and mutable platform state remain in the unchanged compiled tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxEdCompilerBounds (Target)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

attribute [local irreducible] RegistrationNativeFullCompiler.compile RegistrationNativePlatformIdentityCtxTyped.handler

/-- Original raw-mode compilation retains the literal indexed Ed create bound with the same full ledger and platform history. -/
theorem run_create_bound (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((simulateQ (r := RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source) callback (RegistrationNativeFullCompiler.compile setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)).run before).IsQueryBoundP
      (Target .create) (budget.cap 1) := by
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work budget bounded 1
  simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  exact RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound (n := n) setup checks wire route representation created credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)
    (budget.cap 1) bill before

/-- Original raw-mode compilation retains the literal indexed Ed sign bound with the same full ledger and platform history. -/
theorem run_sign_bound (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((simulateQ (r := RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source) callback (RegistrationNativeFullCompiler.compile setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)).run before).IsQueryBoundP
      (Target .sign) (3 * budget.cap 2) := by
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work budget bounded 2
  simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  exact RegistrationNativePlatformIdentityCtxTypedEdBounds.program_sign_bound (n := n) setup checks wire route representation created credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)
    (budget.cap 2) bill before
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds.run_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds.run_create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds.run_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds.run_sign_bound
