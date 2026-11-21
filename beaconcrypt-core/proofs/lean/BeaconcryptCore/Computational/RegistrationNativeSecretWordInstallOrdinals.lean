-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace

/-! The symbolic installation ordinal keeps its original descriptor until evaluation. Native evaluation maps each successful installation message at the same role ordinal and leaves its original public handle unchanged. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordFrontendTrace (Event)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeInterface (Entry)

def messages (role : Role) (events : List Event) : List Message :=
  events.filterMap fun event => match event with
    | .install installed message => if installed = role then some message else none
    | _ => none

def At (role : Role) (events : List Event) (transcript : List Entry) (index : Nat)
    (message : Message) (handle : PqxdhDeploymentInterface.Handle) : Prop :=
  (messages role events)[index]? = some message ∧
    (RegistrationNativeInstallOrdinals.handles role transcript)[index]? = some handle

/-- Concatenating chronological traces concatenates the successful descriptor list in each role. -/
theorem messages_append (role : Role) (first last : List Event) :
    messages role (first ++ last) = messages role first ++ messages role last := by
  exact List.filterMap_append

/-- Evaluation maps every symbolic successful message at its original ordinal. -/
theorem messages_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (role : Role) (events : List Event) :
    RegistrationNativeInstallOrdinals.messages role (events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) =
      (messages role events).map (RegistrationNativeSecretWordMessage.eval candidate) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp only [List.map_cons, RegistrationNativeSecretWordCheckedTrace.event,
        RegistrationNativeInstallOrdinals.messages, messages, List.filterMap_cons] at *
      all_goals first | exact ih | split <;> simp_all

/-- The same successful original Word message/handle pair remains paired at its native evaluated installation ordinal. -/
theorem at_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (role : Role) (events : List Event)
    (transcript : List Entry) (index : Nat) (message : Message) (handle : PqxdhDeploymentInterface.Handle)
    (installed : At role events transcript index message handle) :
    RegistrationNativeInstallOrdinals.At role (events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      transcript index (RegistrationNativeSecretWordMessage.eval candidate message) handle := by
  refine ⟨?_, installed.2⟩
  rw [messages_eval, List.getElem?_map, installed.1, Option.map_some]
end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals.messages_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals.messages_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals.messages_eval' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals.messages_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals.at_eval' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallOrdinals.at_eval
