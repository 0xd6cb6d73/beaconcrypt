-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol

/-! Actual Protocol support discharges the public cursor's successful-install domain receipt. The proof applies before any private service interpretation and retains the actual charged capability sequence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorProtocol
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftProtocol (Control)
open RegistrationNativeHiddenJointCursor (Domain Installed)
variable {n : Nat}

/-- Successful actual Protocol installations name a physical owner allocated before the query. -/
theorem query_installed (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (before : Control n) (result : (WorldSpec n).Range query × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run before)) :
    Installed query result.1 result.2.owners.length := by
  have length := RegistrationNativeHiddenAllocationProtocol.query_length decode route query before result supported
  have growth : before.owners.length ≤ result.2.owners.length := by rw [length]; omega
  cases query with
  | inl created => trivial
  | inr query => cases query with
    | inr record => trivial
    | inl effect => cases effect with
      | inl coin => trivial
      | inr capability => cases capability with
        | installBeacon index metadata reference =>
            intro successful
            have reached : (true, result.2) ∈ support
                ((PqxdhRecordLiftProtocol.effects (.inr (.installBeacon index metadata reference))).run before) := by
              change result ∈ support
                ((PqxdhRecordLiftProtocol.effects (.inr (.installBeacon index metadata reference))).run before) at supported
              have same : result = (true, result.2) := Prod.ext successful rfl
              exact same ▸ supported
            have present := RegistrationNativeHiddenAllocationProtocol.effects_install_beacon_present index metadata reference
              before result.2 reached
            exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp present).1 growth
        | _ => trivial

/-- Every actual Protocol query keeps the public cursor domain inside the same reached physical allocation. -/
theorem query_domain (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (before : Control n) (result : (WorldSpec n).Range query × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run before))
    (shell : CborRecordWorldClient.Shell) (valid : Domain shell before.owners.length) :
    Domain (CborRecordWorldClient.next query result.1 shell) result.2.owners.length := by
  have length := RegistrationNativeHiddenAllocationProtocol.query_length decode route query before result supported
  apply RegistrationNativeHiddenJointCursor.next_domain query result.1 shell before.owners.length _
    (by rw [length]; omega) valid
  exact query_installed decode route query before result supported

end BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorProtocol
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorProtocol.query_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorProtocol.query_installed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorProtocol.query_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorProtocol.query_domain
