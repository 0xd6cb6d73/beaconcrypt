-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallStep
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! Full-ledger installation invariants use the actual native state, its retained installation trace, and physical hidden slots. The local callback contract supplies complete supported raw transitions, including every failed poststate. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallLedger
open PqxdhRecordLiftInterface (Slot)
open RegistrationNativeG2Trace (Event)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeInstallOrdinals (Counts Hidden)
variable {n : Nat} {NativeState : Type}

def Holds (events : NativeState → List Event)
    (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (Slot n))
    (valid : NativeState → Prop) (selected : Message → Prop)
    (state : RegistrationNativeLedger.State × NativeState) : Prop :=
  valid state.2 ∧ (∀ role, Counts role (events state.2) state.1.transcript) ∧
    Hidden (events state.2) state.1.transcript (slots state.2) selected

def Forward (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (Slot n))
    (before after : NativeState) : Prop :=
  ∀ handle, (slots before handle).isSome → (slots after handle).isSome

def Storage (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (Slot n))
    (valid : NativeState → Prop) (before after : NativeState) : Prop :=
  valid after ∧ Forward slots before after

/-- Forward physical storage composes through the same supported callback cuts. -/
theorem forward_trans (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (Slot n))
    (before middle after : NativeState) (first : Forward slots before middle) (last : Forward slots middle after) :
    Forward slots before after := fun handle present => last handle (first handle present)

end BeaconcryptCore.Computational.RegistrationNativeInstallLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallLedger.forward_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallLedger.forward_trans
