-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
/-! A successful current Server build appends exactly the stored Ready descriptor to its own installation trace under any persistent Word interpretation. The free source receipt retains the original reply, platform state, failed prefixes and full raw ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
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

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
open RegistrationNativeSecretWordInstallOrdinals (messages)
local notation "traceState" => RegistrationNativePlatformLorStatefulSupport.TracedState
  (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "traceTyped" => RegistrationNativePlatformLorStatefulSupport.traced implementation controller

/-- Actual private interpretation keeps that same complete callback and its original returned reply. -/
theorem interpreted (handle : Nat) (application : Option (Slice U8)) (before after : traceState)
    (ready : RegistrationNativeSecretWordMessage.ServerReady) (stored : before.1.1.server.sessions[handle]?=some (some ready))
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support ((traceTyped (.inr (.build handle application))).run before)) :
    messages .server after.2.1.events=messages .server before.2.1.events++[ready.reference] :=
  RegistrationNativePlatformSecretWordInstallPeerTraced.build setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    handle application before.1 ready stored before.2.1 ((.ok (some (keyId,bytes)),after.1),after.2.1)
    (RegistrationNativePlatformLorStatefulSupport.traced_support implementation controller (.inr (.build handle application)) before (.ok (some (keyId,bytes)),after) supported)
    keyId bytes rfl

/-- The original full raw ledger records that same descriptor at its actual successful linked build. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (handle : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (before after : RegistrationNativeLedger.State × traceState)
    (ready : RegistrationNativeSecretWordMessage.ServerReady) (stored : before.2.1.1.server.sessions[handle]?=some (some ready))
    (supported : (some response,after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped (.inl (.inr (.build handle payload)))).run before)) :
    messages .server after.2.2.1.events=messages .server before.2.2.1.events++[ready.reference] := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,equal⟩ := supported
  have replyEq : reply=some response := congrArg Prod.fst equal
  have stateEq : current=after.2 := congrArg (fun output => output.2.2) equal
  subst reply
  rw [stateEq] at reached
  exact interpreted setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation handle (RegistrationNativeRawAdapter.application payload)
    before.2 after.2 ready stored response.keyId response.serialized
    (RegistrationNativeTargetRawSuccess.build (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped handle payload response before.2 after.2 reached)

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer.interpreted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer.full
