-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall
/-! The literal corrected public frontend, adaptive program and canonical raw compiler preserve the minimal constructor-kind monitor. Both known and hidden installs match the optional slot origin of the raw material reply most recently demanded by that actual source callback. This structural property makes no alias-exclusion or cryptographic security claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerTypedHandles
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform I KemSK A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept

/-- The actual typed frontend appends exactly the handles in its same original successful typed reply, for both roles and every failed path. -/
theorem handler (role : PqxdhRecordLiftInterface.Role) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform) (indexed : RegistrationNativeHiddenAllocationOwners.Indexed before.1.beacons)
    (trace : List PqxdhDeploymentInterface.Handle)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform) × List PqxdhDeploymentInterface.Handle)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler role)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation query).run before))).run trace)) :
    result.2=trace++RegistrationNativeInstallOrdinals.handles role [RegistrationNativeInstallTypedEntry.entry query result.1.1] := by
  have quiet (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : ¬RegistrationNativePublicCaps.IsMaterial request)
      (noHandle : ∀reply,RegistrationNativeInstallOrdinals.handles role [RegistrationNativeInstallTypedEntry.entry request reply]=[])
      (result : (RegistrationNativeRawAdapter.TypedSpec.Range request × State source Platform) × List PqxdhDeploymentInterface.Handle)
      (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler role)
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper implementation request).run before))).run trace)) :
      result.2=trace++RegistrationNativeInstallOrdinals.handles role [RegistrationNativeInstallTypedEntry.entry request result.1.1] := by
    rw [RegistrationNativePlatformRecordPartnerSnapshotHandles.free role _
      (RegistrationNativePlatformPublicOrdinaryInstall.handler_free (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation role request ordinary before),support_map] at supported
    obtain ⟨actual,_reached,rfl⟩ := supported
    simp only [noHandle,List.append_nil]
  cases query with
  | inl coin=>exact quiet (.inl coin) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
  | inr query=>cases query with
    | build handle application=>
      cases role with
      | server=>
        have counted := RegistrationNativePlatformRecordPartnerServerTyped.build setup source sign view failure allocation reservePeer erased helper implementation handle application before trace result supported
        rw [counted]
        congr 1
        cases result.1.1 with
        | fail error | div=>rfl
        | ok optional=>cases optional <;> rfl
      | beacon=>
        simp only [RegistrationNativePlatformPublicFrontend.handler] at supported
        rw [RegistrationNativePlatformRecordPartnerServerOtherRole.build_handles setup source sign view failure allocation reservePeer erased helper implementation handle application before trace,support_map] at supported
        obtain ⟨actual,_reached,rfl⟩ := supported
        simp [RegistrationNativeInstallTypedEntry.entry,RegistrationNativeInstallOrdinals.handles]
    | finish index packet=>
      have counted := RegistrationNativePlatformRecordPartnerBeaconTyped.finish role setup wire index packet before indexed trace result supported
      rw [counted]
      congr 1
      cases role <;> cases result.1.1 with
      | fail error | div=>rfl
      | ok optional=>cases optional <;> rfl
    | create edPin mlPin keyId=>exact quiet (.inr (.create edPin mlPin keyId)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | bundle index=>exact quiet (.inr (.bundle index)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | accept packet=>exact quiet (.inr (.accept packet)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | hmac key bytes=>exact quiet (.inr (.hmac key bytes)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | hash bytes=>exact quiet (.inr (.hash bytes)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | serverSend keyId plaintext=>exact quiet (.inr (.serverSend keyId plaintext)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | serverRaw raw=>exact quiet (.inr (.serverRaw raw)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | beaconSend index plaintext=>exact quiet (.inr (.beaconSend index plaintext)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
    | beaconRaw index raw=>exact quiet (.inr (.beaconRaw index raw)) (by simp [RegistrationNativePublicCaps.IsMaterial]) (fun _=>by cases role <;> rfl) result supported
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerTypedHandles
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerTypedHandles.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerTypedHandles.handler
