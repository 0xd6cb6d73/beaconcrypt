-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent
/-! Successful Native accept entries retain their raw packet and handle under the original ledger's ML-pin erasure and registration filter. The internal append invariant therefore proves exactly the original public matching scanner's raw uniqueness, without a parser, crypto or enrollment premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeAcceptHandleProjection
open RegistrationNativeInterface (Entry)
open RegistrationNativeAcceptHandleLedger (success Holds)
open PqxdhDeploymentServerAuthEvent (Reg regOfEntry regsOf)

private theorem original_accept (entry : PqxdhDeploymentInterface.Entry) (raw : Pqxdh.Bytes) (handle : Nat)
    (selected : regOfEntry entry = some (Reg.accept raw (some handle))) :
    entry = (⟨.inl (.inr (.accept raw)), some handle⟩ : PqxdhDeploymentInterface.Entry) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases selected
  · cases command with
    | create pin keyId =>
      cases reply with
      | none => cases selected
      | some index =>
        cases parsed : PqxdhDeploymentInterface.parsePin pin <;> simp [regOfEntry, parsed] at selected
    | accept bytes => cases selected; rfl
    | _ => cases selected
  · cases selected

private theorem erased_accept (entry : Entry) (raw : Pqxdh.Bytes) (handle : Nat)
    (same : entry.erase = (⟨.inl (.inr (.accept raw)), some handle⟩ : PqxdhDeploymentInterface.Entry)) :
    success entry = some (raw, handle) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

private theorem accept_member (transcript : List Entry) (raw : Pqxdh.Bytes) (handle : Nat)
    (member : Reg.accept raw (some handle) ∈ regsOf (transcript.map Entry.erase)) :
    ∃ entry ∈ transcript, success entry = some (raw, handle) := by
  obtain ⟨old, oldMember, selected⟩ := List.mem_filterMap.mp member
  have oldEntry := original_accept old raw handle selected
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp oldMember
  exact ⟨entry, nativeMember, erased_accept entry raw handle (erased.trans oldEntry)⟩

/-- The same actual original registration view has at most one raw packet per successful session handle. -/
theorem unique_raw (transcript : List Entry) (count : Nat) (valid : Holds transcript count)
    (raw other : Pqxdh.Bytes) (handle : Nat)
    (left : Reg.accept raw (some handle) ∈ regsOf (transcript.map Entry.erase))
    (right : Reg.accept other (some handle) ∈ regsOf (transcript.map Entry.erase)) : raw = other := by
  obtain ⟨leftEntry, leftMember, leftSuccess⟩ := accept_member transcript raw handle left
  obtain ⟨rightEntry, rightMember, rightSuccess⟩ := accept_member transcript other handle right
  exact RegistrationNativeAcceptHandleLedger.unique_raw transcript count valid leftEntry leftMember rightEntry rightMember
    raw other handle leftSuccess rightSuccess

end BeaconcryptCore.Computational.RegistrationNativeAcceptHandleProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptHandleProjection.unique_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptHandleProjection.unique_raw
