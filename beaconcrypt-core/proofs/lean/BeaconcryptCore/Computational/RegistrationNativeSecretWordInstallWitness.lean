-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotoneFull

/-! A successful same-callback descriptor suffix and the original prefix count identify the same public handle at a final installation ordinal. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordFrontendTrace (Event)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordInstallOrdinals (messages At)
open RegistrationNativeInstallOrdinals (handles)

/-- The actual callback's appended descriptor is paired with its appended original public handle at the same final role ordinal. -/
theorem at_append (role : Role) (before events : List Event) (pre transcript : List RegistrationNativeInterface.Entry)
    (message : Message) (handle : PqxdhDeploymentInterface.Handle)
    (tail : List Message) (later : List PqxdhDeploymentInterface.Handle)
    (count : (messages role before).length = (handles role pre).length)
    (installed : messages role events = messages role before ++ message :: tail)
    (recorded : handles role transcript = handles role pre ++ handle :: later) :
    ∃ ordinal, At role events transcript ordinal message handle := by
  refine ⟨(messages role before).length, ?_, ?_⟩
  · rw [installed]
    simp
  · rw [recorded, count]
    simp
end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness.at_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness.at_append
