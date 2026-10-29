-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete

/-! The representative original public entries retain exactly the literal successful typed handles. These finite calculations connect Rust optional success to the role-local ordinal filters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallOrdinals (handles)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationNativeRawAdapter (resultOption responseOption)

theorem build_length (role : Role) (session : Nat) (application : Option (Slice U8))
    (reply : RustM (Option (U64 × Pqxdh.Bytes))) :
    (handles role [entry (.inr (.build session application)) reply]).length =
      if role = .server ∧ present reply = true then 1 else 0 := by
  cases role <;> cases reply with
  | fail error | div => simp [entry, handles, resultOption, responseOption, present]
  | ok reply => cases reply <;> simp [entry, handles, resultOption, responseOption, present]

theorem build_handle (role : Role) (session : Nat) (application : Option (Slice U8))
    (reply : RustM (Option (U64 × Pqxdh.Bytes))) (position : Nat) (handle : PqxdhDeploymentInterface.Handle)
    (found : (handles role [entry (.inr (.build session application)) reply])[position]? = some handle) :
    ∃ keyId bytes, reply = .ok (some (keyId, bytes)) ∧ handle = .peer keyId := by
  cases role <;> cases reply with
  | fail error | div => simp [entry, handles, resultOption, responseOption] at found
  | ok reply => cases reply with
    | none => simp [entry, handles, resultOption, responseOption] at found
    | some value =>
        rcases value with ⟨keyId, bytes⟩
        cases position <;> simp [entry, handles, resultOption, responseOption] at found
        all_goals
          subst handle
          exact ⟨keyId, bytes, rfl, rfl⟩

theorem finish_length (role : Role) (owner : Nat) (packet : Option registration.ResponsePacket)
    (reply : RustM (Option Pqxdh.Bytes)) :
    (handles role [entry (.inr (.finish owner packet)) reply]).length =
      if role = .beacon ∧ present reply = true then 1 else 0 := by
  cases role <;> cases reply with
  | fail error | div => simp [entry, handles, resultOption, present]
  | ok reply => cases reply <;> simp [entry, handles, resultOption, present]

theorem finish_handle (role : Role) (owner : Nat) (packet : Option registration.ResponsePacket)
    (reply : RustM (Option Pqxdh.Bytes)) (position : Nat) (handle : PqxdhDeploymentInterface.Handle)
    (found : (handles role [entry (.inr (.finish owner packet)) reply])[position]? = some handle) :
    handle = .owner owner := by
  cases role <;> cases reply with
  | fail error | div => simp [entry, handles, resultOption] at found
  | ok reply => cases reply with
    | none => simp [entry, handles, resultOption] at found
    | some value => cases position <;> simpa [entry, handles, resultOption] using found.symm

end BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.build_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.build_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.build_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.build_handle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.finish_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.finish_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.finish_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles.finish_handle
