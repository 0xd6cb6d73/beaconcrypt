-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint

/-! The public cursor domain stays within the actual Protocol owner allocation. Cursor updates preserve existing addresses; successful installation is the sole update that can add an address, and native admission requires that owner already exist. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat}

def Domain (shell : CborRecordWorldClient.Shell) (length : Nat) : Prop :=
  ∀ index cursor, shell.owners index = some cursor → index < length

/-- Empty startup has no public owner cursor. -/
theorem initial (length : Nat) : Domain CborRecordWorldClient.initial length := by
  intro index cursor found
  cases found

/-- Allocating more physical owners preserves every existing cursor's domain bound. -/
theorem mono (shell : CborRecordWorldClient.Shell) (first second : Nat) (bound : first ≤ second)
    (valid : Domain shell first) : Domain shell second :=
  fun index cursor found => Nat.lt_of_lt_of_le (valid index cursor found) bound

/-- The actual send cursor transition changes only a cursor that already existed. -/
theorem advance (shell : CborRecordWorldClient.Shell) (length index : Nat) (plaintext : Pqxdh.Bytes)
    (valid : Domain shell length) : Domain (CborRecordWorldClient.advanceOwner shell index plaintext) length := by
  intro other cursor found
  by_cases same : other = index
  · subst other
    simp only [CborRecordWorldClient.advanceOwner, Function.update_self] at found
    obtain ⟨previous, present, _sameCursor⟩ := Option.map_eq_some_iff.mp found
    exact valid index previous present
  · simp only [CborRecordWorldClient.advanceOwner, Function.update_of_ne same] at found
    exact valid other cursor found

/-- A cursor installation at an actually allocated physical owner retains the public domain bound. -/
theorem install (shell : CborRecordWorldClient.Shell) (length index : Nat) (cursor : CborRecordWorldClient.Cursor)
    (valid : Domain shell length) (allocated : index < length) :
    Domain { shell with owners := Function.update shell.owners index (some cursor) } length := by
  intro other current found
  by_cases same : other = index
  · subst other
    exact allocated
  · simp only [Function.update_of_ne same] at found
    exact valid other current found

/-- The cursor's domain condition implies absence at every missing physical owner index. -/
theorem absent (shell : CborRecordWorldClient.Shell) (owners : List (PqxdhRecordLiftWorldCompiler.Phase n))
    (valid : Domain shell owners.length) (index : Nat) (missing : owners[index]? = none) : shell.owners index = none := by
  cases found : shell.owners index with
  | none => rfl
  | some cursor =>
      have allocated := valid index cursor found
      have outside := List.getElem?_eq_none_iff.mp missing
      omega


/-- Absence at every missing physical owner is the full public cursor-domain condition. -/
theorem of_absent (shell : CborRecordWorldClient.Shell) (owners : List (PqxdhRecordLiftWorldCompiler.Phase n))
    (missing : ∀ index, owners[index]? = none → shell.owners index = none) : Domain shell owners.length := by
  intro index cursor found
  by_contra outside
  have absentOwner : owners[index]? = none := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt outside)
  rw [missing index absentOwner] at found
  cases found

def Installed (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query) (length : Nat) : Prop :=
  match query with
  | .inr (.inl (.inr (.installBeacon index _ _))) => (show Bool from reply) = true → index < length
  | _ => True

/-- Every literal public cursor transition preserves its domain when physical owner allocation grows and a successful install names an allocated owner. -/
theorem next_domain (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query)
    (shell : CborRecordWorldClient.Shell) (first second : Nat) (growth : first ≤ second)
    (valid : Domain shell first) (installed : Installed query reply second) :
    Domain (CborRecordWorldClient.next query reply shell) second := by
  have prior := mono shell first second growth valid
  cases query with
  | inl created =>
      simp only [CborRecordWorldClient.next]
      cases shell.server <;> exact prior
  | inr query => cases query with
    | inl effect => cases effect with
      | inl coin => exact prior
      | inr capability => cases capability with
        | peerPresent keyId | ownerPresent owner | appendOwner sender identity phase | advanceOwner owner phase | hash bytes => exact prior
        | installServer keyId identity reference =>
            cases reply <;> exact prior
        | installBeacon index metadata reference =>
            cases reply with
            | false => exact prior
            | true =>
                exact install shell second index _ prior (installed rfl)
    | inr record => cases record with
      | inl server => cases server <;> exact prior
      | inr beacon =>
          rcases beacon with ⟨index, plaintext | raw⟩
          · exact advance shell second index plaintext prior
          · exact prior

end BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.initial' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.mono
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.advance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.install' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.install
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.absent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.next_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.next_domain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.of_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursor.of_absent
