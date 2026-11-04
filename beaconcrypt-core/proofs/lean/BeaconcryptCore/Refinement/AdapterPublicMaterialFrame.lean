-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime
import BeaconcryptCore.Computational.RegistrationNativeBundlePhases
/-! Untouched SDK objects retain their source material relation through exact private-pool and owner-slot frames. Owner identity is obtained from the actual indexed lookup and metadata/phase maps, not from public-key uniqueness. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicMaterialFrame
open BeaconcryptCore.Computational
open AdapterPublicWrapperState
open RegistrationNativeBeaconFrontend (Owner)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

theorem pool (view : MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (before after : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : Beacon view joint before self owner world) (keys : after.keys=before.keys) :
    Beacon view joint after self owner world := by
  refine ⟨related.identityPublic,related.identitySecret,related.mldsa,related.pin,
    related.serverPublic,related.identifier,?_⟩
  simpa only [Phase,KemPair,keys] using related.phase

theorem beacon (view : MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (before after : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner current : Owner source) (oldSlot newSlot : Option PqxdhRecordLiftBeacon.Phase)
    (related : Beacon view joint before self owner oldSlot)
    (keys : after.keys=before.keys)
    (fields : RegistrationNativeOwnerFields.metadata current=RegistrationNativeOwnerFields.metadata owner)
    (phase : current.phase=owner.phase) (slot : newSlot=oldSlot) :
    Beacon view joint after self current newSlot := by
  rw [slot]
  exact AdapterPublicBundleMaterialLifetime.unchanged view joint after self owner current oldSlot
    (pool view joint before after self owner oldSlot related keys) fields phase

omit material ed in
theorem other_owner (target index : Nat) (different : index≠target)
    (before after : List (Owner source)) (reply : RustM (Option Pqxdh.Bytes))
    (metadata : after.map RegistrationNativeOwnerFields.metadata=before.map RegistrationNativeOwnerFields.metadata)
    (shape : RegistrationNativeBundlePhases.Shape target before reply after)
    (owner : Owner source) (selected : before[index]?=some owner) :
    ∃current,after[index]?=some current ∧
      RegistrationNativeOwnerFields.metadata current=RegistrationNativeOwnerFields.metadata owner ∧
      current.phase=owner.phase := by
  have found : (after.map RegistrationNativeOwnerFields.metadata)[index]?=some (RegistrationNativeOwnerFields.metadata owner) := by
    rw [metadata,List.getElem?_map,selected]
    rfl
  rw [List.getElem?_map] at found
  obtain ⟨current,currentFound,fields⟩ := Option.map_eq_some_iff.mp found
  refine ⟨current,currentFound,fields,?_⟩
  have phases : (RegistrationNativeBundlePhases.phases after)[index]?=
      (RegistrationNativeBundlePhases.phases before)[index]? := by
    rcases shape with same | ⟨bytes,_returned,same⟩
    · exact congrArg (fun values =>values[index]?) same
    · have selectedMap :=  congrArg (fun values =>values[index]?) same
      simpa only [RegistrationNativeBundlePhases.masked,List.getElem?_set_ne (Ne.symm different)] using selectedMap
  simpa only [RegistrationNativeBundlePhases.phases,List.getElem?_map,currentFound,selected,
    Option.map_some,Option.some.injEq] using phases

end BeaconcryptCore.Refinement.AdapterPublicMaterialFrame
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicMaterialFrame.pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicMaterialFrame.pool
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicMaterialFrame.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicMaterialFrame.beacon
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicMaterialFrame.other_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicMaterialFrame.other_owner
