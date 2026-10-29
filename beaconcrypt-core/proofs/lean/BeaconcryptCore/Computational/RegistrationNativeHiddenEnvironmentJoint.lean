-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld

/-! Concrete allocation correspondence for the actual thin frontend and the shared Protocol World. Local owners, private KEM handles and physical World handles remain different types of data; their reached index agreement and the absence of phantom cursors are explicit operational invariants. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint
variable {n : Nat} {KemSK ProviderState Secret : Type} {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK ProviderState Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeHiddenEnvironmentWorld.State n
    (RegistrationNativeHiddenEnvironment.State n KemSK ProviderState source) Secret

structure Holds (state : State n KemSK ProviderState Secret source) : Prop where
  length : state.1.2.owners.length = state.1.1.1.1.beacons.length
  indexed : ∀ (index : Nat) (owner : RegistrationNativePublicOwners.Owner source),
    state.1.1.1.1.beacons[index]? = some owner → owner.view.worldOwner = index
  cursor : ∀ index, state.1.2.owners[index]? = none → state.1.1.2.owners index = none

/-- A missing actual local owner is also missing from the same reached Protocol owner roster. -/
theorem world_missing (state : State n KemSK ProviderState Secret source) (valid : Holds state)
    (index : Nat) (missing : state.1.1.1.1.beacons[index]? = none) : state.1.2.owners[index]? = none := by
  apply List.getElem?_eq_none_iff.mpr
  rw [valid.length]
  exact List.getElem?_eq_none_iff.mp missing

/-- Missing local owners have no cursor in that same reached shared World. -/
theorem cursor_missing (state : State n KemSK ProviderState Secret source) (valid : Holds state)
    (index : Nat) (missing : state.1.1.1.1.beacons[index]? = none) : state.1.1.2.owners index = none :=
  valid.cursor index (world_missing state valid index missing)

/-- Literal empty startup rosters and the empty cursor satisfy the concrete allocation invariant. -/
theorem empty (state : State n KemSK ProviderState Secret source)
    (frontend : state.1.1.1.1.beacons = []) (world : state.1.2.owners = [])
    (cursor : state.1.1.2.owners = fun _ => none) : Holds state := by
  constructor
  · simp only [frontend, world, List.length_nil]
  · intro index owner found
    simp only [frontend, List.getElem?_nil] at found
    cases found
  · intro index _missing
    rw [cursor]

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint.world_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint.world_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint.cursor_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint.cursor_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint.empty
