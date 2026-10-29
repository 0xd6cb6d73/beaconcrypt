-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask

/-! Private restoration after public packing replaces precisely the selected scalar and public prekey. These pure equations preserve every other owner field and identify the actual native roster used by the source interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (PeerEncoding)
open RegistrationNativePublicSourceState (owners)
variable {source : RegistrationNativeMldsa.Source}

def mask (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (before : RegistrationNativeBeaconFrontend.State source) : RegistrationNativeBeaconFrontend.State source :=
  before.mapIdx fun index owner => if index = selected then
    { owner with prekeyScalar := scalar, prekeyPublic := PqxdhRootTableInitialization.rootArray publicPrekey }
    else owner

/-- The private challenge reconstructs exactly the two selected prekey fields after packing. -/
theorem restore_pack (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (before : RegistrationNativeBeaconFrontend.State source) :
    owners scalar (RegistrationNativePublicOwners.pack selected publicPrekey before) = mask selected scalar publicPrekey before := by
  apply List.ext_getElem?
  intro index
  simp only [owners, RegistrationNativePublicOwners.pack, mask, List.getElem?_map, List.getElem?_mapIdx]
  cases found : before[index]? with
  | none => rfl
  | some original =>
      simp only [Option.map_some]
      by_cases chosen : index = selected
      · simp only [chosen, ite_true, RegistrationNativePublicSourceState.owner, Option.getD_none]
        rfl
      · simp only [chosen, ite_false, RegistrationNativePublicSourceState.owner, Option.getD_some,
          RegistrationBeaconReferenceCompiler.restore_erase]

/-- A canonical public roster restores to a fixed point of its private native mask. -/
theorem mask_restored (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (before : RegistrationNativePublicOwners.State source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected publicPrekey before) :
    mask selected scalar publicPrekey (owners scalar before) = owners scalar before := by
  rw [← restore_pack, RegistrationNativePublicOwnerMask.pack_restore selected publicPrekey scalar before canonical]

/-- A native birth preserves every previous masked owner and changes only the selected new position. -/
theorem mask_append (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (before : RegistrationNativeBeaconFrontend.State source) (born : RegistrationNativeBeaconFrontend.Owner source) :
    mask selected scalar publicPrekey (before ++ [born]) = mask selected scalar publicPrekey before ++
      [if before.length = selected then { born with prekeyScalar := scalar, prekeyPublic := PqxdhRootTableInitialization.rootArray publicPrekey } else born] := by
  exact List.mapIdx_concat

/-- Changing the private fallback scalar leaves the publicly packed canonical input unchanged. -/
theorem restored_dummy (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (before : RegistrationNativePublicOwners.State source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected publicPrekey before) :
    mask selected scalar publicPrekey (before.map RegistrationNativePublicOwners.restore) = owners scalar before := by
  change mask selected scalar publicPrekey (owners RegistrationNativePublicOwners.dummy before) = _
  rw [← restore_pack, RegistrationNativePublicOwnerMask.pack_restore selected publicPrekey RegistrationNativePublicOwners.dummy before canonical]

end BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.restore_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.restore_pack
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.mask_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.mask_restored
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.mask_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.mask_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.restored_dummy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore.restored_dummy
