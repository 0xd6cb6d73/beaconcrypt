-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallStep
import BeaconcryptCore.Computational.RegistrationNativeRawAdapter

/-! Typed callback receipts retain only the successful handle shape of their original raw ledger entry. Application bytes and response parsing remain in the actual callbacks; this finite representative is used solely for the ordinal filters. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry
open RegistrationNativeRawAdapter (TypedSpec resultOption responseOption)
open RegistrationNativeInterface (Entry)
open RegistrationNativeInstallOrdinals (handles)
variable {n : Nat}

def entry : (query : TypedSpec.Domain) → TypedSpec.Range query → Entry
  | .inr (.build handle _), reply => ⟨.inl (.inr (.build handle none)), responseOption reply⟩
  | .inr (.finish owner _), reply => ⟨.inl (.inr (.finish owner [])), resultOption reply⟩
  | _, _ => ⟨.inl (.inr (.accept [])), none⟩

/-- Replacing a callback's representative entry by its actual original raw entry preserves its exact suffix receipt whenever the successful handle list is equal. -/
theorem change_entry (role : PqxdhRecordLiftInterface.Role)
    (beforeEvents afterEvents : List RegistrationNativeG2Trace.Event) (first second : Entry)
    (slots : PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (selected : RegistrationNativeRelatedFamily.Message → Prop)
    (same : handles role [first] = handles role [second])
    (prior : RegistrationNativeInstallStep.RoleStep role beforeEvents afterEvents first slots selected) :
    RegistrationNativeInstallStep.RoleStep role beforeEvents afterEvents second slots selected := by
  simpa only [RegistrationNativeInstallStep.RoleStep, same] using prior

end BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry.change_entry' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry.change_entry
