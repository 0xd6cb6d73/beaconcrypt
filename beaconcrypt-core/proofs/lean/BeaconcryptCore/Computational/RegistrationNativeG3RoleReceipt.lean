-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
import BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant

/-! The slot allocator is injective on full literal inputs. Consequently a privately audited earlier use of the current slot/role is an actual earlier successful native installation of that same protected input. Appending the current attempted installation therefore produces the conservative G2 repeated-role event. This is a concrete trace-to-marker implication; it does not assume that the event is negligible or that the second native insertion succeeds. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeG2Trace (Event RepeatedRoleAttempt)
open PqxdhRecordLiftInterface (Slot Role)
variable {n : Nat}

def Recorded (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (slots : Pqxdh.Bytes → Option (Slot n)) (events : List Event) (slot : Slot n) (role : Role) : Prop :=
  ∃ message bytes, Event.install role message ∈ events ∧ input message = some bytes ∧
    slots bytes = some slot ∧ inside bytes = true

/-- An audited role marker at a literal alias yields the actual chronological earlier-success/later-attempt event. -/
theorem attempt_of_recorded (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (before : RegistrationNativeHiddenService.State n)
    (injective : RegistrationNativeHiddenServiceInvariant.InjectiveSlots before)
    (events : List Event) (slot : Slot n) (role : Role) (current : Message) (bytes : Pqxdh.Bytes)
    (realized : input current = some bytes) (allocated : before.slots bytes = some slot)
    (recorded : Recorded input inside before.slots events slot role) :
    RepeatedRoleAttempt input inside (events ++ [.installAttempt role current]) := by
  obtain ⟨earlier, oldBytes, member, oldInput, oldSlot, protectedInput⟩ := recorded
  have same : oldBytes = bytes := injective oldBytes bytes slot oldSlot allocated
  subst oldBytes
  obtain ⟨earlierEvents, middle, split⟩ := List.mem_iff_append.mp member
  refine ⟨earlierEvents, middle, [], role, earlier, current, bytes, ?_, oldInput, realized, protectedInput⟩
  rw [split]
  simp only [List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

/-- Absence of the conservative trace event supplies the unused-role receipt needed by the actual hidden installation. -/
theorem unused_of_no_attempt (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (before : RegistrationNativeHiddenService.State n)
    (injective : RegistrationNativeHiddenServiceInvariant.InjectiveSlots before)
    (events : List Event) (used : Slot n → Role → Bool)
    (history : ∀ slot role, used slot role = true → Recorded input inside before.slots events slot role)
    (slot : Slot n) (role : Role) (current : Message) (bytes : Pqxdh.Bytes)
    (realized : input current = some bytes) (allocated : before.slots bytes = some slot)
    (safe : ¬RepeatedRoleAttempt input inside (events ++ [.installAttempt role current])) :
    used slot role = false := by
  apply Bool.eq_false_iff.mpr
  intro active
  exact safe (attempt_of_recorded input inside before injective events slot role current bytes realized allocated
    (history slot role active))

/-- A successful native installation creates the precise trace receipt when its protected demanded input has a persistent slot. -/
theorem record_success (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (slots : Pqxdh.Bytes → Option (Slot n)) (events : List Event) (slot : Slot n) (role : Role)
    (message : Message) (bytes : Pqxdh.Bytes) (realized : input message = some bytes)
    (allocated : slots bytes = some slot) (protectedInput : inside bytes = true) :
    Recorded input inside slots (events ++ [.install role message]) slot role :=
  ⟨message, bytes, List.mem_append_right events (by simp), realized, allocated, protectedInput⟩

end BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt.attempt_of_recorded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt.attempt_of_recorded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt.unused_of_no_attempt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt.unused_of_no_attempt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt.record_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RoleReceipt.record_success
