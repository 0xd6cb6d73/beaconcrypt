-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-! Shared final-state ordinal interface: successful installation messages and original successful public handles are filtered separately for each physical role. Attempts, demands and failed public replies do not contribute an ordinal. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals
open PqxdhRecordLiftInterface (Role Slot)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeG2Trace (Event)
open RegistrationNativeInterface (Entry)

def messages (role : Role) (events : List Event) : List Message :=
  events.filterMap fun event => match event with
    | .install installed message => if installed = role then some message else none
    | _ => none

def handles (role : Role) (transcript : List Entry) : List PqxdhDeploymentInterface.Handle :=
  transcript.filterMap fun entry => match role, entry with
    | .server, ⟨.inl (.inr (.build _ _)), some response⟩ => some (.peer response.keyId)
    | .beacon, ⟨.inl (.inr (.finish owner _)), some _⟩ => some (.owner owner)
    | _, _ => none

def Counts (role : Role) (events : List Event) (transcript : List Entry) : Prop :=
  (messages role events).length = (handles role transcript).length

def At (role : Role) (events : List Event) (transcript : List Entry) (index : Nat)
    (message : Message) (handle : PqxdhDeploymentInterface.Handle) : Prop :=
  (messages role events)[index]? = some message ∧ (handles role transcript)[index]? = some handle

def Hidden {n : Nat} (events : List Event) (transcript : List Entry)
    (slots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop) : Prop :=
  ∀ role index message handle, At role events transcript index message handle → selected message → (slots handle).isSome

theorem messages_append (role : Role) (first last : List Event) :
    messages role (first ++ last) = messages role first ++ messages role last := by
  exact List.filterMap_append

theorem handles_append (role : Role) (first last : List Entry) :
    handles role (first ++ last) = handles role first ++ handles role last := by
  exact List.filterMap_append

end BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals.messages_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals.messages_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals.handles_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals.handles_append
