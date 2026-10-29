-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicOwners

/-! Exact owner-index correspondence is preserved by the real public-owner erasure and restoration. Appending a native owner assigned the actual preceding physical length extends that correspondence without identifying KEM handles or requiring distinct public credentials. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
variable {source : RegistrationNativeMldsa.Source}

def NativeIndexed (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∀ index (owner : RegistrationNativeBeaconFrontend.Owner source), owners[index]? = some owner → owner.worldOwner = index

def Indexed (owners : RegistrationNativePublicOwners.State source) : Prop :=
  ∀ index (owner : RegistrationNativePublicOwners.Owner source), owners[index]? = some owner → owner.view.worldOwner = index

/-- The empty actual local owner list has no mismatched physical address. -/
theorem empty : Indexed ([] : RegistrationNativePublicOwners.State source) := by
  intro index owner found
  cases found

/-- An actual appended owner retains the allocator's old local length as its physical address. -/
theorem append (owners : RegistrationNativeBeaconFrontend.State source) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (valid : NativeIndexed owners) (assigned : owner.worldOwner = owners.length) : NativeIndexed (owners ++ [owner]) := by
  intro index current found
  by_cases earlier : index < owners.length
  · exact valid index current (by simpa only [List.getElem?_append_left earlier] using found)
  · have equal : index = owners.length := by
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst index
    simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at found
    subst current
    exact assigned

/-- Restoring selected or ordinary owners retains their literal physical addresses. -/
theorem restore (owners : RegistrationNativePublicOwners.State source) (valid : Indexed owners) :
    NativeIndexed (owners.map RegistrationNativePublicOwners.restore) := by
  intro index owner found
  rw [List.getElem?_map] at found
  obtain ⟨original, present, changed⟩ := Option.map_eq_some_iff.mp found
  subst owner
  exact valid index original present

/-- Erasing the selected scalar and replacing only its public prekey retain every actual physical address. -/
theorem pack (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) (valid : NativeIndexed owners) :
    Indexed (RegistrationNativePublicOwners.pack selected publicPrekey owners) := by
  intro index owner found
  rw [RegistrationNativePublicOwners.pack, List.getElem?_mapIdx] at found
  obtain ⟨original, present, changed⟩ := Option.map_eq_some_iff.mp found
  by_cases chosen : index = selected <;> simp only [chosen, ite_true, ite_false] at changed
  all_goals subst owner; exact valid index original present

/-- Public scalar erasure leaves the complete roster length unchanged. -/
theorem pack_length (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) :
    (RegistrationNativePublicOwners.pack selected publicPrekey owners).length = owners.length := by
  simp only [RegistrationNativePublicOwners.pack, List.length_mapIdx]

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.restore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.pack
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.pack_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners.pack_length
