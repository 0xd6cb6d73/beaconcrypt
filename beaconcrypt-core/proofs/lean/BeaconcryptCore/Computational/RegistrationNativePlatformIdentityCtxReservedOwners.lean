-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
import BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedOwners
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativePlatformIdentityCtxMain (Full)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned native)
variable {n count : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

/-- Every final source owner has its exact reserved family index, irrespective of whether that owner existed at an earlier acceptance. -/
theorem owner (joint : PqxdhJointIdentity.Primitives) (seeds : Fin count → IdentitySeed)
    (router : PqxdhDynamicIdentityRouting.PublicState) (capacity : router.created ≤ count)
    (before : Full n KemSK Platform source) (owned : Owned joint before)
    (pool : before.2.1 = PqxdhDynamicIdentityRouting.sourceState seeds router)
    (selected : RegistrationNativeIdentityFrontend.Owner source) (member : selected ∈ before.1.1.beacons) :
    ∃ index : Fin count, index.val = selected.identity.handle ∧ selected.identity.publicIdentity = joint.publicKeys (seeds index) := by
  change RegistrationNativeIdentityRealization.Owned joint before.2.1 before.1.1.beacons at owned
  obtain ⟨seed, found, publicKey⟩ := owned selected member
  have born : selected.identity.handle < router.created := by
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [pool, PqxdhDynamicIdentityRouting.sourceState_length seeds router capacity] at bound
    exact bound
  have finite : selected.identity.handle < count := born.trans_le capacity
  let index : Fin count := ⟨selected.identity.handle, finite⟩
  have reserved := PqxdhDynamicIdentityRouting.sourceState_lookup seeds router selected.identity.handle born finite
  rw [pool] at found
  have same : seed = seeds index := Option.some.inj (found.symm.trans reserved)
  exact ⟨index, rfl, by simpa only [same] using publicKey⟩

/-- A tuple accepted under any identity in the final realized native roster names a reserved alias, including future-created owners and repeated public keys. -/
theorem native_key (joint : PqxdhJointIdentity.Primitives) (seeds : Fin count → IdentitySeed)
    (router : PqxdhDynamicIdentityRouting.PublicState) (capacity : router.created ≤ count)
    (before : Full n KemSK Platform source) (owned : Owned joint before)
    (pool : before.2.1 = PqxdhDynamicIdentityRouting.sourceState seeds router)
    (position : Nat) (identity : PqxdhEd25519EufCma.Ed25519PublicKey)
    (found : ((native before).1.beacons.map fun current => (joint.publicKeys current.identitySeed).ed25519)[position]? = some identity) :
    ∃ index : Fin count, (joint.publicKeys (seeds index)).ed25519 = identity := by
  simp only [RegistrationNativePlatformIdentityCtxLifecycle.native, RegistrationNativePlatformIdentityCtxMain.project,
    RegistrationNativePlatformIdentityMain.project, RegistrationNativeIdentityMainSource.project,
    RegistrationNativeIdentityRealization.owners, List.map_map] at found
  change (before.1.1.beacons.map fun current =>
    (joint.publicKeys (RegistrationNativeIdentityRealization.seedFor before.2.1 current.identity)).ed25519)[position]? = some identity at found
  rw [List.getElem?_map] at found
  obtain ⟨selected, present, equal⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_getElem? present
  obtain ⟨index, _handle, publicKey⟩ := owner joint seeds router capacity before owned pool selected member
  change RegistrationNativeIdentityRealization.Owned joint before.2.1 before.1.1.beacons at owned
  obtain ⟨seed, stored, same⟩ := owned selected member
  rw [RegistrationNativeIdentityRealization.seed_found before.2.1 selected.identity seed stored, ← same, publicKey] at equal
  exact ⟨index, equal⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedOwners.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedOwners.owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedOwners.native_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedOwners.native_key
