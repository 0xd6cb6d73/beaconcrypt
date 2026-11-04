-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinFrontend
/-! The actual source owner mask and pending-pin invariant hold through arbitrary stateful World closing. The source callback bodies supply both invariant steps. No state-frame or whole interpreted-controller equation is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSecretWordOrdinary (State)
variable {n : Nat} {I KemSK Platform E Private Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

def Holds (selected : Nat) (prekey : PqxdhJointIdentity.PeerEncoding) (before : State source Platform) : Prop :=
  RegistrationNativePublicOwnerMask.Canonical selected prekey before.1.beacons ∧
    RegistrationNativeSecretWordPendingPin.Holds before.1.beacons

theorem query (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range request × State source Platform)
    (prior : Holds selectedOwner publicPrekey before)
    (supported : result ∈ support ((controller request).run before)) : Holds selectedOwner publicPrekey result.2 :=
  ⟨RegistrationNativePlatformSecretWordPrekeyMask.query setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer request before result prior.1 supported,
   RegistrationNativePlatformSecretWordPendingPin.query setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer request before result prior.2 supported⟩

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller
local notation "InterpretedState" => RegistrationNativePlatformLorStatefulSupport.State (State source Platform) Private

theorem typed_holds (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : InterpretedState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range request × InterpretedState)
    (prior : Holds selectedOwner publicPrekey before.1)
    (supported : result ∈ support ((typed request).run before)) : Holds selectedOwner publicPrekey result.2.1 :=
  RegistrationNativePlatformLorSourceFrame.typed_preserves implementation controller (Holds selectedOwner publicPrekey)
    (query setup checks wire sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    request before result prior supported

theorem path_holds (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × InterpretedState} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after)
    (prior : Holds selectedOwner publicPrekey before.2.1) : Holds selectedOwner publicPrekey after.2.1 :=
  RegistrationNativePlatformLorSourceFrame.path_preserves implementation controller (Holds selectedOwner publicPrekey)
    (query setup checks wire sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    setup.source.crypto wire serverKeyId bounds actual prior
theorem run_initialized (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : InterpretedState) (ownersEmpty : before.1.1.beacons=[])
    (result : RegistrationNativeEvents.Observed Value InterpretedState)
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds selectedOwner publicPrekey result.2.2.1 := by
  rw [RegistrationNativeFullCompiler.compile_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  have prior : Holds selectedOwner publicPrekey before.1 := by
    constructor
    · rw [ownersEmpty]
      exact RegistrationNativePublicOwnerMask.empty _ _
    · rw [ownersEmpty]
      intro index owner found
      simp only [List.getElem?_nil] at found
      cases found
  have kept := RegistrationNativePlatformLorSourceFrame.program_preserves implementation controller (Holds selectedOwner publicPrekey)
    (query setup checks wire sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    _ before reached prior called
  cases returned
  exact kept

theorem path_pin (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × InterpretedState} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after) :
    after.2.1.1.server.pin=before.2.1.1.server.pin := by
  apply RegistrationNativePlatformLorSourceFrame.path_preserves implementation controller
    (fun current => current.1.server.pin=before.2.1.1.server.pin) _ setup.source.crypto wire serverKeyId bounds actual rfl
  intro request first next prior reached
  exact (RegistrationNativePlatformSecretWordServerPinFrontend.query setup checks wire sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer request first next reached).trans prior

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.typed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.typed_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.path_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.path_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.run_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.run_initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.path_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies.path_pin
