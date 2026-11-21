-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Carrier Objects SourceSnapshot BeaconTable TokenTable)
variable {n : Nat} {KemSK Platform R : Type} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
open RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun (Sample)

omit material platform ed in
private theorem projected (old : RawCtxWholeOwner.OwnerState Unit)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (reply : Option beaconcrypt_record_send.shared.Encrypted) :
    RegistrationNativePlatformExtractedSdkOrdinarySendCommon.project old (.ok (kernel,reply))=
      (RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply reply,{old with owner:={old.owner with kernel:=kernel}}) := by
  unfold RegistrationNativePlatformExtractedSdkOrdinarySendCommon.project
  dsimp only [Function.comp_apply]
  rw [RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_projection]
  rfl

def nextWorld (before : PqxdhRecordLiftWorld.State n) (worldOwner : Nat)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (reached : Sample Platform) : PqxdhRecordLiftWorld.State n :=
  PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag worldOwner) reached.1.2.2
    {before with owners:=before.owners.set worldOwner (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) kernel)
                 ownerRaw:=Function.update before.ownerRaw worldOwner (before.ownerRaw worldOwner)
                 primitive:=reached.1.2.1}

def next (before : Native) (worldOwner : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (reached : Sample Platform) : Native ×Platform :=
  (RegistrationNativePlatformOrdinaryExperiment.replaceWorld before
    (nextWorld before.server.world.world.1 worldOwner self control binding kernel reached),reached.2)

def returned (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) : beaconcrypt_public_wrapper.beacon.Beacon :=
  {self with state:=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel)}

def update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=mlSource) R)
    (logical worldOwner : Nat) (rawBefore : Native) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (reached : Sample Platform) : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=mlSource) R :=
  {before with beacons:=Function.update before.beacons logical (some (returned self control binding kernel))
               snapshot:=.direct (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed worldOwner self
                 (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source rawBefore worldOwner self control binding reached)).2}

omit platform in
theorem native_eq (before : Native) (worldOwner : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (initial final : ratchet.concrete.ConcreteRatchetKernel) (reply : Option beaconcrypt_record_send.shared.Encrypted)
    (reached : Sample Platform) (normal : reached.1.1=.ok (final,reply)) :
    RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.native before worldOwner self control binding initial reached=
      (RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply reply,next before worldOwner self control binding final reached) := by
  unfold RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.native RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.project
    RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.finish
  rw [normal,projected]
  rfl

noncomputable def put (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native ×Platform) (before : Carrier (R:=R) view containers joint created credential current)
    (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (selected : current.1.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons logical=some self)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (initial final : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager initial))
    (completed : RegistrationBeaconSeed.PublicCompleted) (phase : owner.phase=.established completed)
    (reply : Option beaconcrypt_record_send.shared.Encrypted) (reached : Sample Platform) (normal : reached.1.1=.ok (final,reply)) :
    Carrier (R:=R) view containers joint created credential (next current.1 owner.worldOwner self control binding final reached) := by
  have original : AdapterPublicWrapperState.Beacon view joint current.1.pool self owner current.1.server.world.world.1.owners[owner.worldOwner]? := by
    have old:=before.beacons logical
    rw [selected] at old
    obtain ⟨actual,found,material⟩:=old
    have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
    subst actual
    exact material
  have facts:=original.phase
  simp only [AdapterPublicWrapperState.Phase,stored,phase] at facts
  have identifier : self.identity_key_kid=binding.assigned_key_id := by
    have actual:=original.identifier
    simp only [AdapterPublicWrapperState.currentId,phase] at actual
    rw [←facts.2.1] at actual
    exact actual
  have address:=before.indexed logical owner selected
  have below : owner.worldOwner<current.1.server.world.world.1.owners.length := by
    rw [address,before.allocated]
    exact (List.getElem?_eq_some_iff.mp selected).1
  refine {
    objects:=update before.objects logical owner.worldOwner current.1 self control binding final reached
    server:={ identity:=before.server.identity
              control:=before.server.control
              pinIdentity:=before.server.pinIdentity
              pinIdentifier:=before.server.pinIdentifier
              pinMldsa:=before.server.pinMldsa
              replay:=before.server.replay
              peers:=before.server.peers }
    beacons:=?_
    tokens:=before.tokens
    sessionCount:=before.sessionCount
    ownerCount:=before.ownerCount
    allocated:=?_
    indexed:=before.indexed
    backend:=?_ }
  · intro otherIndex
    change match current.1.beacons[otherIndex]? with
    | none=>Function.update before.objects.beacons logical (some (returned self control binding final)) otherIndex=none
    | some other=>∃sourceSelf,Function.update before.objects.beacons logical (some (returned self control binding final)) otherIndex=some sourceSelf ∧
        AdapterPublicWrapperState.Beacon view joint current.1.pool sourceSelf other
          (nextWorld current.1.server.world.world.1 owner.worldOwner self control binding final reached).owners[other.worldOwner]?
    by_cases same:otherIndex=logical
    · subst otherIndex
      rw [selected]
      refine ⟨returned self control binding final,Function.update_self _ _ _,?_⟩
      change AdapterPublicWrapperState.Beacon view joint current.1.pool (returned self control binding final) owner
        (current.1.server.world.world.1.owners.set owner.worldOwner
          (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) final))[owner.worldOwner]?
      rw [List.getElem?_set_self below]
      have active:=AdapterPublicOrdinaryKernel.material_preserved view joint current.1.pool self owner
        current.1.server.world.world.1.owners[owner.worldOwner]? original control binding (AdapterPublicOrdinaryEnvelope.manager initial) stored completed phase final
      simpa only [returned,RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell,identifier,AdapterPublicOrdinaryEnvelope.manager] using active
    · rw [Function.update_of_ne same]
      cases found:current.1.beacons[otherIndex]? with
      | none=>simpa only [found] using before.beacons otherIndex
      | some other=>
          have old:=before.beacons otherIndex
          rw [found] at old
          obtain ⟨oldSelf,oldStored,oldMaterial⟩:=old
          refine ⟨oldSelf,oldStored,?_⟩
          have otherAddress:=before.indexed otherIndex other found
          have different : owner.worldOwner≠other.worldOwner := by rw [address,otherAddress];exact Ne.symm same
          change AdapterPublicWrapperState.Beacon view joint current.1.pool oldSelf other
            (current.1.server.world.world.1.owners.set owner.worldOwner
              (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) final))[other.worldOwner]?
          rw [List.getElem?_set_ne different]
          exact oldMaterial
  · change (current.1.server.world.world.1.owners.set owner.worldOwner _).length=current.1.beacons.length
    rw [List.length_set]
    exact before.allocated
  · change RegistrationNativePlatformSdkReification.persistent
      (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed owner.worldOwner self
        (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source current.1 owner.worldOwner self control binding reached)).2=
      RegistrationNativePlatformSdkReification.persistent (next current.1 owner.worldOwner self control binding final reached)
    unfold RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source
    simp only [RegistrationNativePlatformExtractedSdkOrdinary.pack,normal,AdapterPublicOrdinaryKernel.returned_exact]
    rfl

theorem put_objects (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native ×Platform) (before : Carrier (R:=R) view containers joint created credential current)
    (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (selected : current.1.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons logical=some self)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (initial final : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager initial))
    (completed : RegistrationBeaconSeed.PublicCompleted) (phase : owner.phase=.established completed)
    (reply : Option beaconcrypt_record_send.shared.Encrypted) (reached : Sample Platform) (normal : reached.1.1=.ok (final,reply)) :
    (put view containers joint created credential current before logical owner selected self sourceSelected control binding initial final
      stored completed phase reply reached normal).objects=
      update before.objects logical owner.worldOwner current.1 self control binding final reached := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.native_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.native_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.put

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.put_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.put_objects
