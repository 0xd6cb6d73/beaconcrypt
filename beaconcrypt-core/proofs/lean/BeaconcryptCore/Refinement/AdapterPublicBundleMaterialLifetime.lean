-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleMaterial
import BeaconcryptCore.Computational.RegistrationNativeBundleTerminal
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
/-! Source private-material relations ignore only chronological Ed signing history while retaining every cryptographic private object, current identifier, full binding and World phase. Exact owner metadata and reached phase reconstruct the current owner, so publication history updates do not invalidate source material. Concrete pending World-slot and selected-owner lookup lemmas account for the actual terminal update. Final whole-run field premises are discharged separately by the actual native bundle proofs. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Owner Phase)
variable {source : RegistrationNativeMldsa.Source}

theorem owner_fields (before after : Owner source) (phase : Phase)
    (fields : RegistrationNativeOwnerFields.metadata after = RegistrationNativeOwnerFields.metadata before)
    (samePhase : after.phase = phase) :
    after = {before with phase, edHistory := after.edHistory} := by
  have copied := congrArg (fun owner : Owner source => ({owner with phase := after.phase, edHistory := after.edHistory} : Owner source)) fields
  change after = {before with phase := after.phase, edHistory := after.edHistory} at copied
  simpa only [samePhase] using copied

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK : Type}
omit platform in
theorem history (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (log : PqxdhJointIdentity.History) :
    AdapterPublicWrapperState.Beacon view joint pool self {owner with edHistory := log} world := by
  refine ⟨related.identityPublic, related.identitySecret, related.pin, related.serverPublic, ?_, ?_⟩
  · simpa only [AdapterPublicWrapperState.currentId] using related.identifier
  · simpa only [AdapterPublicWrapperState.Phase] using related.phase

omit platform in
theorem installed (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner current : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (identifier : AdapterPublicWrapperState.currentId owner = owner.pin.binding.identity_key_id)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekeyView : AdapterPublicWrapperState.KxPair view prekey owner.prekeyScalar owner.prekeyPublic)
    (oneTimeView : view.kxSecret oneTime.secret_key = scalar)
    (kemView : AdapterPublicWrapperState.KemPair view pool kem owner.kemHandle owner.kemPublic)
    (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (fields : RegistrationNativeOwnerFields.metadata current = RegistrationNativeOwnerFields.metadata owner)
    (samePhase : current.phase = .initSent finished.pending scalar) :
    AdapterPublicWrapperState.Beacon view joint pool {self with state := .InitSent finished.pending prekey oneTime kem}
      current (some (.inactive .initSent)) := by
  rw [owner_fields owner current _ fields samePhase]
  exact history view joint pool _ _ _
    (AdapterPublicBundleMaterial.installed_related view joint pool self owner world related identifier prekey oneTime kem scalar prekeyView oneTimeView kemView finished) current.edHistory

omit platform in
theorem unchanged (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner current : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (fields : RegistrationNativeOwnerFields.metadata current = RegistrationNativeOwnerFields.metadata owner)
    (samePhase : current.phase = owner.phase) :
    AdapterPublicWrapperState.Beacon view joint pool self current world := by
  rw [owner_fields owner current _ fields samePhase]
  exact history view joint pool self owner world related current.edHistory

omit material platform ed in
theorem advanced_owner (world : PqxdhRecordLiftWorld.State n) (index : Nat)
    (ready : RegistrationNativeBundleTerminal.Ready world index) :
    (RegistrationNativeBundleTerminal.advancedWorld index world).owners[index]? = some (.inactive .initSent) := by
  have within : index < world.owners.length := by
    rcases ready with fresh | supplied
    · exact (List.getElem?_eq_some_iff.mp fresh).1
    · exact (List.getElem?_eq_some_iff.mp supplied).1
  exact List.getElem?_set_self within

omit material platform ed in
theorem after_owner (index : Nat) (owner current : Owner source) (pending : registration.BeaconPending)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationNativeExperiment.State n KemSK source)
    (selected : before.beacons[index]? = some current) :
    (RegistrationNativeBundleTerminal.after index owner pending scalar before).beacons[index]? = some {current with phase := .initSent pending scalar} := by
  change (RegistrationNativeFinishTerminal.setPhase index _ before.beacons)[index]? = _
  simp only [RegistrationNativeFinishTerminal.setPhase, selected]
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp selected).1

end BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.owner_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.owner_fields

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.history

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.installed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.unchanged

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.advanced_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.advanced_owner

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.after_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime.after_owner
