-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenServiceInvariant

/-! Concrete demand receipts retain the thin service's literal-address allocator and actual demand counter through public material sampling and all native rejection branches. A hidden reply is tied to its protected realized full input and persistent slot; no source kernel or private seed enters this service. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand
open RegistrationNativeHiddenService (State reserve material demand)
open RegistrationNativeHiddenServiceInvariant (Ordered InjectiveSlots)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeRelatedFamily (Message)
variable {n : Nat}

/-- Reservation itself changes no demand counter; the demand callback already charged it once. -/
theorem reserve_count (bytes : Pqxdh.Bytes) (before : State n) : (reserve bytes before).2.demands = before.demands := by
  unfold reserve
  split
  · rfl
  · split <;> rfl

/-- Every real material read retains the allocator and records exactly its returned public44 bytes. -/
theorem material_fields (slot : Slot n) (before after : State n) (value : Material)
    (supported : (value, after) ∈ support ((material slot).run before)) :
    after.prepared = before.prepared ∧ after.slots = before.slots ∧ after.next = before.next ∧
      after.demands = before.demands ∧ after.materials slot = some value := by
  cases found : before.materials slot with
  | some cached =>
      rw [RegistrationNativeHiddenService.material_hit slot before cached found, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, rfl, rfl, rfl, found⟩
  | none =>
      rw [RegistrationNativeHiddenService.material_miss slot before found, support_map] at supported
      obtain ⟨sampled, _possible, equal⟩ := supported
      cases equal
      exact ⟨rfl, rfl, rfl, rfl, QueryCache.cacheQuery_self _ _ _⟩

/-- Every actual demand charges once and preserves the derived allocator invariants, including missing preparation and overflow. -/
theorem demand_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : State n) (reply : Option (RegistrationNativePairedChoice.Choice n))
    (ordered : Ordered before) (injective : InjectiveSlots before)
    (supported : (reply, after) ∈ support ((demand source input inside message).run before)) :
    after.demands = before.demands + 1 ∧ Ordered after ∧ InjectiveSlots after := by
  let counted := { before with demands := before.demands + 1 }
  have calls : before.next ≤ before.demands := ordered.2.1
  have countedOrdered : Ordered counted := ⟨ordered.1, by dsimp only [counted]; omega, ordered.2.2⟩
  have countedInjective : InjectiveSlots counted := injective
  by_cases prepared : before.prepared message = true
  · simp only [demand, StateT.run, prepared, ite_true] at supported
    cases realized : input message with
    | none =>
        simp only [realized, mem_support_pure_iff] at supported
        cases supported
        exact ⟨rfl, countedOrdered, countedInjective⟩
    | some bytes =>
        by_cases protectedInput : inside bytes = true
        · simp only [realized, protectedInput, ite_true] at supported
          have nextOrdered := RegistrationNativeHiddenServiceInvariant.reserve_ordered bytes before ordered
          have nextInjective := RegistrationNativeHiddenServiceInvariant.reserve_injective bytes before ordered injective
          have nextCount := reserve_count bytes counted
          cases allocated : reserve bytes counted with
          | mk selected reached =>
              change _ ∈ support (match reserve bytes counted with
                | (none, final) => pure (none, final)
                | (some slot, final) => (fun result : Material × State n =>
                    (some (RegistrationNativePairedChoice.Choice.hidden ⟨slot, result.1⟩), result.2)) <$>
                      (material slot).run final) at supported
              rw [allocated] at supported
              change Ordered (reserve bytes counted).2 at nextOrdered
              change InjectiveSlots (reserve bytes counted).2 at nextInjective
              rw [allocated] at nextOrdered nextInjective nextCount
              cases selected with
              | none =>
                  simp only [mem_support_pure_iff] at supported
                  cases supported
                  exact ⟨nextCount, nextOrdered, nextInjective⟩
              | some slot =>
                  simp only [support_map] at supported
                  obtain ⟨⟨value, final⟩, materialSupport, equal⟩ := supported
                  cases equal
                  have fields := material_fields slot reached final value materialSupport
                  exact ⟨fields.2.2.2.1.trans nextCount,
                    RegistrationNativeHiddenServiceInvariant.material_keeps slot reached final value nextOrdered nextInjective materialSupport⟩
        · simp only [realized, ite_eq_right protectedInput, mem_support_pure_iff] at supported
          cases supported
          exact ⟨rfl, countedOrdered, countedInjective⟩
  · simp only [demand, StateT.run, ite_eq_right prepared, mem_support_pure_iff] at supported
    cases supported
    exact ⟨rfl, countedOrdered, countedInjective⟩

/-- Every hidden service reply retains its actual protected descriptor-to-slot association and material cache receipt. -/
theorem hidden_receipt (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : State n) (reference : RegistrationNativePairedDemand.Reference n)
    (supported : (some (.hidden reference), after) ∈ support ((demand source input inside message).run before)) :
    ∃ bytes, input message = some bytes ∧ inside bytes = true ∧
      after.slots bytes = some reference.slot ∧ after.materials reference.slot = some reference.material := by
  by_cases prepared : before.prepared message = true
  · simp only [demand, StateT.run, prepared, ite_true] at supported
    cases realized : input message with
    | none => simp only [realized, mem_support_pure_iff] at supported; cases supported
    | some bytes =>
        by_cases protectedInput : inside bytes = true
        · simp only [realized, protectedInput, ite_true] at supported
          let counted := { before with demands := before.demands + 1 }
          cases allocated : reserve bytes counted with
          | mk selected reached =>
              change _ ∈ support (match reserve bytes counted with
                | (none, final) => pure (none, final)
                | (some slot, final) => (fun result : Material × State n =>
                    (some (RegistrationNativePairedChoice.Choice.hidden ⟨slot, result.1⟩), result.2)) <$>
                      (material slot).run final) at supported
              rw [allocated] at supported
              cases selected with
              | none => simp only [mem_support_pure_iff] at supported; cases supported
              | some slot =>
                  simp only [support_map] at supported
                  obtain ⟨⟨value, final⟩, materialSupport, equal⟩ := supported
                  cases equal
                  have fields := material_fields slot reached final value materialSupport
                  have recorded := RegistrationNativeHiddenServiceInvariant.reserve_records bytes counted slot (congrArg Prod.fst allocated)
                  rw [allocated] at recorded
                  exact ⟨bytes, rfl, protectedInput, (congrFun fields.2.1 bytes).trans recorded, fields.2.2.2.2⟩
        · simp only [realized, ite_eq_right protectedInput, mem_support_pure_iff] at supported
          cases supported
  · simp only [demand, StateT.run, ite_eq_right prepared, mem_support_pure_iff] at supported
    cases supported

end BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.reserve_count' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.reserve_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.material_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.material_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.demand_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.demand_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.hidden_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand.hidden_receipt
