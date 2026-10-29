-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenService

/-! The actual thin service allocates slots in first-touch order by literal full input. Its derived range/injectivity invariants prevent unrelated addresses from sharing a slot, and its real demand counter discharges finite overflow under the eventual whole-client bill. Preparation and public material sampling retain the allocator. These are service invariants, not an assumption that repeated-role aliases cannot occur. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant
open RegistrationNativeHiddenService (State reserve prepare material)
open PqxdhRecordLiftInterface (Slot)
variable {n : Nat}

def Ordered (before : State n) : Prop :=
  before.next ≤ n ∧ before.next ≤ before.demands ∧
    ∀ bytes slot, before.slots bytes = some slot → slot.val < before.next

def InjectiveSlots (before : State n) : Prop :=
  ∀ left right slot, before.slots left = some slot → before.slots right = some slot → left = right

private def paired (before : State n) : RegistrationNativePairedServices.State n :=
  ⟨before.slots, before.next, before.demands, (before.materials, ⟨0, 0⟩), PqxdhRecordLiftWorld.initial⟩

private theorem reserve_paired (bytes : Pqxdh.Bytes) (before : State n) :
    paired (reserve bytes { before with demands := before.demands + 1 }).2 =
      (RegistrationNativePairedServices.reserve bytes (paired before)).2 := by
  cases found : before.slots bytes with
  | some slot => simp only [reserve, RegistrationNativePairedServices.reserve, paired, found]
  | none =>
      by_cases room : before.next < n
      · simp only [reserve, RegistrationNativePairedServices.reserve, paired, found, dite_eq_left room]
      · simp only [reserve, RegistrationNativePairedServices.reserve, paired, found, dite_eq_right room]

/-- Empty thin startup has no address assignment and satisfies the concrete first-touch range invariant. -/
theorem initial : Ordered (RegistrationNativeHiddenService.initial (n := n)) ∧
    InjectiveSlots (RegistrationNativeHiddenService.initial (n := n)) := by
  constructor
  · simp [Ordered, RegistrationNativeHiddenService.initial]
  · intro left right slot missing
    cases missing

/-- The allocator preserves the actual range/demand ordering after the real counted demand prefix. -/
theorem reserve_ordered (bytes : Pqxdh.Bytes) (before : State n) (ordered : Ordered before) :
    Ordered (reserve bytes { before with demands := before.demands + 1 }).2 := by
  have actual := RegistrationNativePairedServices.reserve_ordered bytes (paired before) ordered
  rw [← reserve_paired] at actual
  exact actual

/-- Distinct literal addresses never acquire the same slot in a well-formed actual allocation. -/
theorem reserve_injective (bytes : Pqxdh.Bytes) (before : State n)
    (ordered : Ordered before) (injective : InjectiveSlots before) :
    InjectiveSlots (reserve bytes { before with demands := before.demands + 1 }).2 := by
  unfold reserve
  split
  · exact injective
  · rename_i missing
    split
    · intro left right slot foundLeft foundRight
      by_cases leftNew : left = bytes <;> by_cases rightNew : right = bytes
      · exact leftNew.trans rightNew.symm
      · subst left
        simp only [Function.update_self, Option.some.injEq] at foundLeft
        simp only [Function.update_of_ne rightNew] at foundRight
        cases foundLeft
        have impossible := ordered.2.2 right _ foundRight
        exact (Nat.lt_irrefl before.next impossible).elim
      · subst right
        simp only [Function.update_self, Option.some.injEq] at foundRight
        simp only [Function.update_of_ne leftNew] at foundLeft
        cases foundRight
        have impossible := ordered.2.2 left _ foundLeft
        exact (Nat.lt_irrefl before.next impossible).elim
      · exact injective left right slot
          ((Function.update_of_ne leftNew _ _).symm.trans foundLeft)
          ((Function.update_of_ne rightNew _ _).symm.trans foundRight)
    · exact injective

/-- A reached demand below the actual slot allowance cannot overflow, including a repeat alias. -/
theorem reserve_some (bytes : Pqxdh.Bytes) (before : State n) (ordered : Ordered before)
    (room : before.demands < n) : ∃ slot, (reserve bytes { before with demands := before.demands + 1 }).1 = some slot := by
  cases found : before.slots bytes with
  | some slot => exact ⟨slot, by simp only [reserve, found]⟩
  | none =>
      have available : before.next < n := ordered.2.1.trans_lt room
      exact ⟨⟨before.next, available⟩, by simp only [reserve, found, dite_eq_left available]⟩

/-- A reserved address has its actual returned persistent slot. -/
theorem reserve_records (bytes : Pqxdh.Bytes) (before : State n) (slot : Slot n)
    (allocated : (reserve bytes before).1 = some slot) : (reserve bytes before).2.slots bytes = some slot := by
  cases found : before.slots bytes with
  | some current =>
      rw [RegistrationNativeHiddenService.reserve_hit bytes before current found] at allocated ⊢
      cases allocated
      exact found
  | none =>
      by_cases room : before.next < n
      · simp only [reserve, found, dite_eq_left room] at allocated ⊢
        cases allocated
        exact Function.update_self _ _ _
      · simp only [reserve, found, dite_eq_right room] at allocated
        cases allocated

/-- Preparation records only its public success flag and retains all allocator invariants. -/
theorem prepare_keeps (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes)
    (message : RegistrationNativeRelatedFamily.Message) (before after : State n) (reply : Option RegistrationNativeRelatedFamily.Message)
    (ordered : Ordered before) (injective : InjectiveSlots before)
    (supported : (reply, after) ∈ support ((prepare input message).run before)) :
    Ordered after ∧ InjectiveSlots after := by
  simp only [RegistrationNativeHiddenService.prepare_run, mem_support_pure_iff] at supported
  cases supported
  exact ⟨ordered, injective⟩

/-- Material44 sampling changes no address, next index or actual demand count. -/
theorem material_keeps (slot : Slot n) (before after : State n) (value : PqxdhDeploymentHiddenLayout.Material)
    (ordered : Ordered before) (injective : InjectiveSlots before)
    (supported : (value, after) ∈ support ((material slot).run before)) :
    Ordered after ∧ InjectiveSlots after := by
  cases found : before.materials slot with
  | some cached =>
      rw [RegistrationNativeHiddenService.material_hit slot before cached found, mem_support_pure_iff] at supported
      cases supported
      exact ⟨ordered, injective⟩
  | none =>
      rw [RegistrationNativeHiddenService.material_miss slot before found, support_map] at supported
      obtain ⟨sampled, _possible, equal⟩ := supported
      cases equal
      exact ⟨ordered, injective⟩

end BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.initial' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_ordered
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_injective
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.reserve_records
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.prepare_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.prepare_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.material_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant.material_keeps
