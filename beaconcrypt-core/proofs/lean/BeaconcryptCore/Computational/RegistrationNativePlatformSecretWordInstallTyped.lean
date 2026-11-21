-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallOrdinals (handles)
variable {n : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Every actual open typed Word callback pairs its exact message suffix count with the same literal public entry. -/
theorem count [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (frontend : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativePlatformSecretWordOrdinary.State source Platform) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run frontend)).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧ added.length = (handles role [entry query result.1.1]).length := by
  have quiet (free : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
      (noHandle : handles role [entry query result.1.1] = []) :
      ∃ added, messages role result.2.events = messages role before.events ++ added ∧ added.length = (handles role [entry query result.1.1]).length := by
    have bill := RegistrationNativeSecretWordInstallTrace.free role _
      (RegistrationNativePlatformSecretWordOtherInstall.other_free setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer role query free frontend)
      before result supported
    exact ⟨[], by simpa only [List.append_nil] using bill, by rw [noHandle]; rfl⟩
  cases query with
  | inl coin => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
  | inr query => cases query with
    | build handle application =>
        obtain ⟨added, bill, counted⟩ := RegistrationNativePlatformSecretWordInstallServerTyped.build_count setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer role handle application frontend before result supported
        exact ⟨added, bill, counted.trans (RegistrationNativeInstallTypedHandles.build_length role handle application result.1.1).symm⟩
    | finish index packet =>
        obtain ⟨added, bill, counted⟩ := RegistrationNativePlatformSecretWordInstallBeaconTyped.finish setup checks wire sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer role index packet frontend before result supported
        exact ⟨added, bill, counted.trans (RegistrationNativeInstallTypedHandles.finish_length role index packet result.1.1).symm⟩
    | create edPin mlPin keyId => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | bundle owner => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | accept packet => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | hmac key message => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | hash bytes => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | serverSend keyId plaintext => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | serverRaw raw => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | beaconSend owner plaintext => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
    | beaconRaw owner raw => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTyped.count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTyped.count
