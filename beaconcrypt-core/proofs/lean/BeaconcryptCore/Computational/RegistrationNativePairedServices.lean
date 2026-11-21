-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationHiddenInstall
import BeaconcryptCore.Computational.RegistrationBeaconSeed
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntryTable

/-! Native paired registration services allocate by the actual complete related-root input, rather than by a descriptor encoding or a projected root. Allocation and material demand are separate from the earlier actual root callback. The finite-capacity branch is explicit. The private seed table is exactly the record World's persistent table; public material replies carry only the assigned slot and position-one material. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedServices
open PqxdhRecordLiftInterface (Slot Role)
open PqxdhDeploymentHiddenLayout (Material joinOutput)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
variable {n : Nat}

abbrev MaterialSpec (n : Nat) := Slot n →ₒ Material

/-- All fields are private interpreter state. No service returns its seed table. -/
structure State (n : Nat) where
  slots : Pqxdh.Bytes → Option (Slot n)
  next : Nat
  demands : Nat
  materials : PqxdhRecordLiftLazyTable.State (MaterialSpec n)
  world : PqxdhRecordLiftWorld.State n

def initial (world : PqxdhRecordLiftWorld.State n) : State n :=
  ⟨fun _ => none, 0, 0, PqxdhRecordLiftLazyTable.initial, world⟩

/-- A first material demand allocates the next slot; every repeated literal input keeps its original slot. Exhaustion returns no slot and never changes an earlier assignment. -/
def reserve (bytes : Pqxdh.Bytes) (before : State n) : Option (Slot n) × State n :=
  match before.slots bytes with
  | some slot => (some slot, { before with demands := before.demands + 1 })
  | none => if room : before.next < n then
      let slot : Slot n := ⟨before.next, room⟩
      (some slot, { before with
        slots := Function.update before.slots bytes (some slot)
        next := before.next + 1
        demands := before.demands + 1 })
    else (none, { before with demands := before.demands + 1 })

/-- Allocated indices lie below the next index; capacity and the actual demand count bound that index. -/
def Ordered (state : State n) : Prop :=
  state.next ≤ n ∧ state.next ≤ state.demands ∧
    ∀ bytes slot, state.slots bytes = some slot → slot.val < state.next

theorem initial_ordered (world : PqxdhRecordLiftWorld.State n) : Ordered (initial world) := by
  simp [Ordered, initial]

theorem reserve_hit (bytes : Pqxdh.Bytes) (before : State n) (slot : Slot n)
    (found : before.slots bytes = some slot) :
    reserve bytes before = (some slot, { before with demands := before.demands + 1 }) := by
  simp only [reserve, found]

theorem reserve_exhausted (bytes : Pqxdh.Bytes) (before : State n)
    (missing : before.slots bytes = none) (full : n ≤ before.next) :
    reserve bytes before = (none, { before with demands := before.demands + 1 }) := by
  simp only [reserve, missing, Nat.not_lt.mpr full, _root_.dite_false]

theorem reserve_receipt (bytes : Pqxdh.Bytes) (before : State n) :
    (reserve bytes before).2.demands = before.demands + 1 ∧
    (reserve bytes before).2.world = before.world ∧
    (reserve bytes before).2.materials = before.materials ∧
    before.next ≤ (reserve bytes before).2.next ∧
    (reserve bytes before).2.next ≤ before.next + 1 := by
  unfold reserve
  split
  · simp
  · split <;> simp

/-- Any earlier literal-input alias survives every later reservation, including overflow. -/
theorem reserve_retains (bytes previous : Pqxdh.Bytes) (before : State n) (slot : Slot n)
    (cached : before.slots previous = some slot) :
    (reserve bytes before).2.slots previous = some slot := by
  unfold reserve
  split
  · exact cached
  · rename_i missing
    split
    · have different : previous ≠ bytes := by
        intro equal
        subst previous
        rw [missing] at cached
        cases cached
      exact (Function.update_of_ne different _ _).trans cached
    · exact cached

theorem reserve_records (bytes : Pqxdh.Bytes) (before : State n) (slot : Slot n)
    (allocated : (reserve bytes before).1 = some slot) :
    (reserve bytes before).2.slots bytes = some slot := by
  cases found : before.slots bytes with
  | some current =>
    rw [reserve_hit bytes before current found] at allocated ⊢
    cases allocated
    exact found
  | none =>
    by_cases room : before.next < n
    · simp only [reserve, found, dite_eq_left room] at allocated ⊢
      cases allocated
      exact Function.update_self _ _ _
    · simp only [reserve, found, dite_eq_right room] at allocated
      cases allocated

theorem reserve_ordered (bytes : Pqxdh.Bytes) (before : State n) (ordered : Ordered before) :
    Ordered (reserve bytes before).2 := by
  rcases ordered with ⟨capacity, calls, indices⟩
  unfold reserve
  split
  · exact ⟨capacity, Nat.le_trans calls (Nat.le_succ _), indices⟩
  · split
    · rename_i room
      refine ⟨room, Nat.succ_le_succ calls, ?_⟩
      intro other slot found
      dsimp! only at found ⊢
      by_cases same : other = bytes
      · subst other
        simp only [Function.update_self, Option.some.injEq] at found
        cases found
        exact Nat.lt_succ_self _
      · rw [Function.update_of_ne same] at found
        exact Nat.lt_trans (indices other slot found) (Nat.lt_succ_self _)
    · exact ⟨capacity, Nat.le_trans calls (Nat.le_succ _), indices⟩

/-- Every actual successful descriptor has exactly the 192 source bytes used as the private alias key. -/
theorem address_width (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (realized : RegistrationNativeRelatedFamily.input joint dh seed scalar message = some bytes) :
    bytes.length = 192 :=
  RegistrationNativeRelatedFamily.input_length joint dh seed scalar message bytes realized

/-- Descriptor aliases coalesce by the complete realized bytes without an encoding or DH injectivity premise. -/
theorem reserve_alias (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (left right : Message) (bytes : Pqxdh.Bytes) (before : State n)
    (leftInput : RegistrationNativeRelatedFamily.input joint dh seed scalar left = some bytes)
    (rightInput : RegistrationNativeRelatedFamily.input joint dh seed scalar right = some bytes) :
    (RegistrationNativeRelatedFamily.input joint dh seed scalar left).map (fun point => reserve point before) =
      (RegistrationNativeRelatedFamily.input joint dh seed scalar right).map (fun point => reserve point before) := by
  rw [leftInput, rightInput]

/-- The actual earlier root callback retains its full family instrumentation and cannot allocate or evaluate a material entry. -/
noncomputable def prepare (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) :
    StateT (RegistrationNativeRelatedFamily.State × State n) ProbComp (Option RootOutput) := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$>
    (RegistrationNativeRelatedRoot.sourceRoot source hmac joint dh seed scalar message).run before.1

theorem prepare_no_demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message)
    (before : RegistrationNativeRelatedFamily.State × State n)
    (result : Option RootOutput × (RegistrationNativeRelatedFamily.State × State n))
    (supported : result ∈ support ((prepare source hmac joint dh seed scalar message).run before)) :
    result.2.2 = before.2 := by
  simp only [prepare, StateT.run, support_map] at supported
  obtain ⟨inner, _reached, rfl⟩ := supported
  rfl

end BeaconcryptCore.Computational.RegistrationNativePairedServices

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.initial_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.initial_ordered
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_exhausted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_exhausted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_records
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_ordered
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.address_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.address_width
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.reserve_alias
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServices.prepare_no_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServices.prepare_no_demand
