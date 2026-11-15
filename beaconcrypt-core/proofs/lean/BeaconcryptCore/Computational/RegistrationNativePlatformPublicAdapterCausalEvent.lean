-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
/-! The causal event reads the final actual source Beacon identity roster. The same material relation derives the exact native identity list, including repeated keys and owners created after the accepted prefix. The historical unsigned-tuple predicate and original transcript are unchanged. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
open RegistrationNativePlatformPublicAdapterSourceRuntime (Objects)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {I KemSK R P Value :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}

omit material platform ed in
private theorem range_lookup {X Y :Type} (function :X→Y) (values :List X) :
    (List.range values.length).filterMap (fun index=>(values[index]?).map function)=values.map function :=by
  induction values with
  | nil=>rfl
  | cons head tail ih=>
    simp only [List.length_cons,List.range_succ_eq_map,List.filterMap_cons,List.getElem?_cons_zero,Option.map_some]
    rw [List.filterMap_map]
    simpa only [Function.comp_def,List.getElem?_cons_succ,List.map_cons] using congrArg (List.cons (function head)) ih

def identity (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) :PqxdhEd25519EufCma.Ed25519PublicKey :=
  ⟨PqxdhRefinement.absBytes (view.edPublic self.identity_key.public_key),by simp⟩

def roster (view :AdapterPublicWrapperState.MaterialView source KemSK) (objects :Objects R) :
    List PqxdhEd25519EufCma.Ed25519PublicKey :=
  (List.range objects.nextOwner).filterMap (fun index=>(objects.beacons index).map (identity view))

variable (setup :PqxdhServerAuthExperiment.Setup base KemSK)
variable (view :AdapterPublicWrapperState.MaterialView source KemSK) (views :AdapterPublicWrapperStorage.Views)
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
variable (current :RegistrationNativeExperiment.State n KemSK source×P)
variable (before :StrongCarrier (R:=R) setup view views created credential current)

theorem identity_source (index :Nat) :
    (before.base.objects.beacons index).map (identity view)=
      (current.1.beacons[index]?).map (fun owner=>(setup.joint.publicKeys owner.identitySeed).ed25519) :=by
  have table:=before.base.beacons index
  cases found:current.1.beacons[index]? with
  | none=>
    simp only [found] at table
    rw [table]
    rfl
  | some owner=>
    simp only [found] at table
    obtain ⟨self,stored,related⟩:=table
    rw [stored]
    simp only [Option.map_some]
    apply congrArg some
    apply Subtype.ext
    change PqxdhRefinement.absBytes (view.edPublic self.identity_key.public_key)=_
    rw [related.identityPublic,PqxdhRootTableInitialization.rootArray_bytes]
    rfl

theorem roster_source :
    roster view (RegistrationNativePlatformPublicAdapterSourceRuntime.objects
      (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects))=
      current.1.beacons.map (fun owner=>(setup.joint.publicKeys owner.identitySeed).ed25519) :=by
  change (List.range before.base.objects.nextOwner).filterMap
    (fun index=>(before.base.objects.beacons index).map (identity view))=_
  rw [before.base.ownerCount]
  have same : (fun index=>(before.base.objects.beacons index).map (identity view))=
      (fun index=>(current.1.beacons[index]?).map (fun owner=>(setup.joint.publicKeys owner.identitySeed).ed25519)) :=by
    funext index
    exact identity_source setup view views created credential current before index
  rw [same]
  exact range_lookup _ current.1.beacons

theorem physical_roster :
    roster view (RegistrationNativePlatformPublicAdapterSourceRuntime.objects
      (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
        (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)))=
      current.1.beacons.map (fun owner=>(setup.joint.publicKeys owner.identitySeed).ed25519) :=
  roster_source setup view views created credential current before

noncomputable def sourceCausal (wire :RegistrationNativeWire.Wire)
    (result :Value×RegistrationNativeLedger.State) (objects :Objects R) :Bool :=by
  classical
  exact decide (RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (roster view objects) result.2.transcript)

theorem event_source (wire :RegistrationNativeWire.Wire) (value :Value) (ledger :RegistrationNativeLedger.State) :
    sourceCausal setup view wire (value,ledger)
      (RegistrationNativePlatformPublicAdapterSourceRuntime.objects
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
          (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)))=
    RegistrationNativeIdentityOriginalCausalInitialized.event (n:=n) setup wire source (value,ledger,current.1) :=by
  unfold sourceCausal RegistrationNativeIdentityOriginalCausalInitialized.event
  rw [physical_roster setup view views created credential current before]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.identity_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.identity_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.roster_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.roster_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.physical_roster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.physical_roster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.event_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent.event_source
