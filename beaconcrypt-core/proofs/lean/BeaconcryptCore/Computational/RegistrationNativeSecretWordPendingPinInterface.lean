-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners

/-! A retained pending controller is checked against that same owner's immutable configured Server pin. This stronger property does not identify a pending binding's copy of the pin with the stored owner pin by assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPin
variable {source : RegistrationNativeMldsa.Source}

def Coherent (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source) : Prop :=
  match owner.phase with
  | .initSent pending _ => pending.control.expected_server_binding = owner.pin.binding
  | _ => True

def Holds (owners : RegistrationNativePublicOwners.State source) : Prop :=
  ∀ (index : Nat) (owner : RegistrationNativePublicOwners.Owner source), owners[index]? = some owner → Coherent owner.view

/-- The indexed retained property is exactly coherence of every actual owner in the roster. -/
theorem holds_iff (owners : RegistrationNativePublicOwners.State source) :
    Holds owners ↔ ∀ owner ∈ owners, Coherent owner.view := by
  constructor
  · induction owners with
    | nil => simp
    | cons first rest ih =>
        intro valid owner member
        rcases List.mem_cons.mp member with rfl | member
        · exact valid 0 _ rfl
        · exact ih (fun index selected found => valid (index + 1) selected
            (by simpa only [List.getElem?_cons_succ] using found)) owner member
  · intro valid index owner found
    exact valid owner (List.mem_of_getElem? found)

/-- The stronger retained invariant gives the actual pending controller's expected binding directly from its indexed owner's stored pin. -/
theorem pending (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source) (valid : Coherent owner)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (phase : owner.phase = .initSent pending oneTime) :
    pending.control.expected_server_binding = owner.pin.binding := by
  simpa only [Coherent, phase] using valid

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPin.holds_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPin.holds_iff
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPin.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPin.pending
