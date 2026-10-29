-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconTyped
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles

/-! Every original Word callback supplies the successful installation count of the literal public reply. This finite open-controller fact covers all owners, ordinary preparation, malformed input and failed callbacks, independently of the private interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallOrdinals (handles)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Every actual open typed Word callback pairs its exact message suffix count with the same literal public entry. -/
theorem count (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (frontend : RegistrationNativeSecretWordMessage.State source) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeSecretWordMessage.State source) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run frontend)).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧ added.length = (handles role [entry query result.1.1]).length := by
  have quiet (free : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
      (noHandle : handles role [entry query result.1.1] = []) :
      ∃ added, messages role result.2.events = messages role before.events ++ added ∧ added.length = (handles role [entry query result.1.1]).length := by
    have bill := RegistrationNativeSecretWordInstallTrace.free role _
      (RegistrationNativeSecretWordAtomServerFrontend.other_free role setup checks wire sign selectedOwner selectedAccept publicPrekey query free frontend)
      before result supported
    exact ⟨[], by simpa only [List.append_nil] using bill, by rw [noHandle]; rfl⟩
  cases query with
  | inl coin => exact quiet (by constructor <;> simp [RegistrationNativeRawAdapter.kind]) (by cases role <;> rfl)
  | inr query => cases query with
    | build handle application =>
        obtain ⟨added, bill, counted⟩ := RegistrationNativeSecretWordInstallServerTyped.build setup checks wire sign selectedOwner selectedAccept publicPrekey
          role handle application frontend before result supported
        exact ⟨added, bill, counted.trans (RegistrationNativeInstallTypedHandles.build_length role handle application result.1.1).symm⟩
    | finish index packet =>
        obtain ⟨added, bill, counted⟩ := RegistrationNativeSecretWordInstallBeaconTyped.finish setup checks wire sign selectedOwner selectedAccept publicPrekey
          role index packet frontend before result supported
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
end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTyped.count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTyped.count
