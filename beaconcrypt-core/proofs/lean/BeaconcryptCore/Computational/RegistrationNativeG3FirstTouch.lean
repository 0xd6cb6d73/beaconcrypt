-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3Tables
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntryTable

/-! The actual G2 key interface has literal coins and108-byte values indexed by input bytes. Its private first-touch allocator retains byte aliases and assigns distinct fresh points successive Fin n slots. A complete slot table answers the same allocator; the total overflow branch remains explicit until the syntactic material cap excludes it. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch
open PqxdhServerAuthKeySchedule (Output)
open PqxdhRecordLiftInterface (Slot)
variable {n : Nat} {Value : Type}

abbrev Spec := PqxdhRegistrationJointKemSecondEntry.Spec Pqxdh.Bytes Output
abbrev Alloc (n : Nat) := PqxdhRegistrationJointKemSecondEntry.Alloc Pqxdh.Bytes n
abbrev Cache (n : Nat) := (Slot n →ₒ Output).QueryCache
abbrev Table (n : Nat) := Slot n → Output

def take (point : Pqxdh.Bytes) (before : Alloc n) : Option (Slot n) × Alloc n :=
  match before.1 point with
  | some slot => (some slot, before)
  | none => if room : before.2 < n then
      (some ⟨before.2, room⟩, (Function.update before.1 point (some ⟨before.2, room⟩), before.2 + 1))
    else (none, before)

noncomputable def fixed (outputs : Table n) : QueryImpl Spec (StateT (Alloc n) ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr point => fun before =>
      let allocated := take point before
      match allocated.1 with
      | some slot => pure (outputs slot, allocated.2)
      | none => (fun answer => (answer, allocated.2)) <$> ($ᵗ Output)

noncomputable def lazySlots : QueryImpl Spec (StateT (Alloc n × Cache n) ProbComp) :=
  PqxdhRegistrationJointKemSecondEntry.slotImpl (R := Output) (fun slot => (Slot n →ₒ Output).randomOracle slot)

/-- An existing literal input reuses its exact earlier slot without changing allocation. -/
theorem take_hit (point : Pqxdh.Bytes) (before : Alloc n) (slot : Slot n)
    (found : before.1 point = some slot) : take point before = (some slot, before) := by
  simp only [take, found]

/-- A fresh input uses precisely the next free slot and extends the private assignment map once. -/
theorem take_miss (point : Pqxdh.Bytes) (before : Alloc n) (absent : before.1 point = none) (room : before.2 < n) :
    take point before = (some ⟨before.2, room⟩,
      (Function.update before.1 point (some ⟨before.2, room⟩), before.2 + 1)) := by
  simp only [take, absent, dite_eq_left room]

/-- Exhaustion is explicit only for an unassigned input; repeated inputs still retain their earlier slot. -/
theorem take_full (point : Pqxdh.Bytes) (before : Alloc n) (absent : before.1 point = none) (full : n ≤ before.2) :
    take point before = (none, before) := by
  simp only [take, absent, dite_eq_right (Nat.not_lt.mpr full)]

/-- Every allocator call adds at most one slot, independently of any table value or primitive reply. -/
theorem take_progress (point : Pqxdh.Bytes) (before : Alloc n) : (take point before).2.2 ≤ before.2 + 1 := by
  unfold take
  split
  · exact Nat.le_succ _
  · split
    · exact le_rfl
    · exact Nat.le_succ _

/-- A positive remaining query budget with room cannot reach the overflow branch. -/
theorem take_some (point : Pqxdh.Bytes) (before : Alloc n) (room : before.2 < n) :
    ∃ slot, (take point before).1 = some slot := by
  cases found : before.1 point with
  | some slot => exact ⟨slot, by rw [take_hit point before slot found]⟩
  | none => exact ⟨⟨before.2, room⟩, by rw [take_miss point before found room]⟩

/-- The source allocator is exactly the existing first-touch slot interpreter with its real lazy slot oracle. -/
theorem lazySlots_eq : lazySlots (n := n) =
    PqxdhRegistrationJointKemSecondEntry.slotImpl (R := Output)
      (fun slot => (Slot n →ₒ Output).randomOracle slot) := rfl

/-- Actual unif coin queries retain the entire private allocator. -/
theorem fixed_coin (outputs : Table n) (coin : Nat) (before : Alloc n) :
    (fixed outputs (.inl coin)).run before = (fun reply => (reply, before)) <$> (unifSpec.query coin : ProbComp _) := by
  simp only [fixed, StateT.run_lift, bind_pure_comp]
  rfl

/-- A value query reads its assigned table cell; only explicit exhaustion reaches the total fallback draw. -/
theorem fixed_point (outputs : Table n) (point : Pqxdh.Bytes) (alloc : Alloc n) :
    (fixed outputs (.inr point)).run alloc =
      match take point alloc with
      | (some slot, after) => pure (outputs slot, after)
      | (none, after) => (fun answer => (answer, after)) <$> ($ᵗ Output) := by
  change (match (take point alloc).1 with
      | some slot => pure (outputs slot, (take point alloc).2)
      | none => (fun answer => (answer, (take point alloc).2)) <$> ($ᵗ Output)) = _
  cases take point alloc with
  | mk selected after => cases selected <;> rfl

/-- The lazy slot version forwards the same coin with both private coordinates retained. -/
theorem lazy_coin (coin : Nat) (before : Alloc n × Cache n) :
    (lazySlots (.inl coin)).run before = (fun reply => (reply, before)) <$> (unifSpec.query coin : ProbComp _) := by
  exact PqxdhRegistrationJointKemSecondEntry.slot_coin _ coin before

end BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_hit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_miss' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_miss
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_full' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_progress' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_progress
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.take_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.lazySlots_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.lazySlots_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.fixed_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.fixed_coin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.fixed_point
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.lazy_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch.lazy_coin
