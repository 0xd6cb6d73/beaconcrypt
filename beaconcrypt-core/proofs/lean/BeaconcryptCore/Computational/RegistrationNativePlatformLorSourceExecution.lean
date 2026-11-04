-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
/-! Exact state reassociation closes the literal current source controller through any persistent Word interpretation. The original value, full native ledger, frontend, public platform state and private interpreter state remain one joint outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution
variable {n : Nat} {KemSK Front Private A : Type}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))

/-- The same adaptive source program retains its complete frontend/private pair under exact persistent interpretation. -/
theorem program_run (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : Front × Private) :
    (simulateQ (RegistrationNativePlatformLorStatefulSupport.typed implementation controller) work).run before =
    (fun result => (result.1.1,(result.1.2,result.2))) <$>
      (simulateQ implementation ((simulateQ controller work).run before.1)).run before.2 := by
  rw [RegistrationNativePlatformLorStatefulSupport.typed,OracleComp.simulateQ_flattenStateT_run,
    ←QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]

open PqxdhServerAuthExperiment (Setup Checks)
variable {I Platform E : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks canonical source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- Literal raw/full compilation preserves the same complete actual source and persistent-interpreter outcome in every mode. -/
theorem full_run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform × Private) :
    RegistrationNativeFullCompiler.run setup.source.crypto canonical serverKeyId bounds
      (RegistrationNativePlatformLorStatefulSupport.typed implementation controller) mode work before =
    (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
      (simulateQ implementation (RegistrationNativePlatformSecretWordFrontend.run setup checks wire source sign
        selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        serverKeyId bounds mode work before.1)).run before.2 := by
  rw [RegistrationNativeFullCompiler.compile_run,program_run,Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution.program_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution.full_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution.full_run
