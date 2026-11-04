-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySendReification
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (M State)
open RegistrationNativePlatformSdkOrdinarySendReification (Compatible)
open RegistrationNativePlatformSdkOrdinarySampleReification (send_sample receive_sample)
open RegistrationNativePlatformSdkOrdinaryReification (primitive journal)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable {n : Nat} {KemSK Platform R I E A B Reader Response Reply PublicReply : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

omit material platform ed in
private theorem pure_compatible (value : A) : Compatible (pure value :M Platform A) := by
  intro before
  simp only [StateT.run_pure,map_pure]
  rfl

omit material platform ed in
private theorem mapped (observe : A →B) (work : M Platform A) (held : Compatible work) : Compatible (observe <$>work) := by
  intro before
  rw [StateT.run_map,StateT.run_map,←held before,Functor.map_map,Functor.map_map]
  rfl

variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

omit material platform ed primitives [FrameDispatchFallback.Operations] in
def rawBefore (before : Store n KemSK R Platform) (index : Nat) : Nat :=before.backend.1.world.ownerRaw index

omit material platform ed primitives [FrameDispatchFallback.Operations] in
def commit (before : Store n KemSK R Platform) (index : Nat) (invoked : Bool) (reached : State) (next : Platform) :
    RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform :=
  ({before.backend.1 with world := (PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag index) reached.2 {before.backend.1.world with ownerRaw:=Function.update before.backend.1.world.ownerRaw index (rawBefore before index+if invoked then 1 else 0), primitive:=primitive reached.1})},next)

omit primitives [FrameDispatchFallback.Operations] in
def finish (before : Store n KemSK R Platform) (index : Nat) (observe : Reply→PublicReply) (invoked : Bool)
    (reached : ((RustM (Reply ×beaconcrypt_public_wrapper.beacon.Beacon) ×State) ×Platform)) :
    RustM (PublicReply ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) :=
  let backend:=commit before index invoked reached.1.2 reached.2
  (match reached.1.1 with
    | .ok word=>.ok (observe word.1,RegistrationNativePlatformPublicAdapterStore.beacon before index word.2 backend)
    | .fail error=>.fail error
    | .div=>.div,backend)

omit primitives [FrameDispatchFallback.Operations] in
theorem commit_snapshot (before : Store n KemSK R Platform) (native : RegistrationNativeExperiment.State n KemSK mlSource) (previous : Platform)
    (basis : before.backend=RegistrationNativePlatformSdkReification.persistent (native,previous))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (index : Nat) (invoked : Bool) (reached : State) (next : Platform) :
    commit before index invoked (journal reached) next=
      RegistrationNativePlatformSdkReification.persistent
        (({returned:=self,raw:=(RegistrationNativePlatformOrdinaryExperiment.replaceWorld native {native.server.world.world.1 with primitive:=reached.1},next),
           owner:=index,frames:=reached.2,rawBefore:=rawBefore before index,rawInvoked:=invoked} :RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon n KemSK Platform mlSource).committed) := by
  have backendEq:=congrArg Prod.fst basis
  unfold commit
  rw [backendEq]
  simp only [RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
    RegistrationNativePlatformSdkReification.worldBackend,RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.committed,
    RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.world,RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.rawAfter,
    RegistrationNativePlatformOrdinaryExperiment.replaceWorld,PqxdhRecordLiftWorld.produce,journal,primitive,Function.update_idem]

omit primitives [FrameDispatchFallback.Operations] in
theorem factor (before : Store n KemSK R Platform) (index : Nat) (observe : Reply→PublicReply)
    (native : RegistrationNativeExperiment.State n KemSK mlSource) (previous : Platform)
    (basis : before.backend=RegistrationNativePlatformSdkReification.persistent (native,previous)) (invoked : Bool)
    (work : M Platform (RustM (Reply ×beaconcrypt_public_wrapper.beacon.Beacon))) (compatible : Compatible work) :
    finish before index observe invoked <$>((work.run (before.backend.1.world.primitive,[])).run before.backend.2)=
    (finish before index observe invoked ∘Prod.map (Prod.map id journal) id) <$>
      ((work.run (native.server.world.world.1.primitive,[])).run previous) := by
  have primitiveEq : before.backend.1.world.primitive=primitive native.server.world.world.1.primitive := by rw [basis];rfl
  have platformEq : before.backend.2=previous := congrArg Prod.snd basis
  have core:=congrArg (fun value=>value.run previous) (compatible (native.server.world.world.1.primitive,[]))
  rw [StateT.run_map] at core
  have lifted:=congrArg (fun distribution=>finish before index observe invoked <$>distribution) core
  simp only [Functor.map_map] at lifted
  rw [primitiveEq,platformEq]
  exact lifted.symm

omit primitives [FrameDispatchFallback.Operations] in
def observed (index : Nat) (fallback : beaconcrypt_public_wrapper.beacon.Beacon)
    (native : RegistrationNativeExperiment.State n KemSK mlSource) (rawCount : Nat) (invoked : Bool)
    (reached : ((RustM (Reply ×beaconcrypt_public_wrapper.beacon.Beacon) ×State) ×Platform)) :
    RustM (Reply ×beaconcrypt_public_wrapper.beacon.Beacon) ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform) :=
  let packet:=RegistrationNativePlatformExtractedSdkOrdinary.pack native rawCount invoked reached
  let self:=match packet.outcome with | .ok word=>word.2 | _=>fallback
  (packet.outcome,(RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.packet packet index self).committed)

omit primitives [FrameDispatchFallback.Operations] in
def update (before : Store n KemSK R Platform) (index : Nat) (observe : Reply→PublicReply)
    (result : RustM (Reply ×beaconcrypt_public_wrapper.beacon.Beacon) ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform)) :
    RustM (PublicReply ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) :=
  let backend:=RegistrationNativePlatformSdkReification.persistent result.2
  (match result.1 with
    | .ok word=>.ok (observe word.1,RegistrationNativePlatformPublicAdapterStore.beacon before index word.2 backend)
    | .fail error=>.fail error
    | .div=>.div,backend)

omit primitives [FrameDispatchFallback.Operations] in
theorem observed_factor (before : Store n KemSK R Platform) (index : Nat) (fallback : beaconcrypt_public_wrapper.beacon.Beacon)
    (observe : Reply→PublicReply) (native : RegistrationNativeExperiment.State n KemSK mlSource) (previous : Platform)
    (basis : before.backend=RegistrationNativePlatformSdkReification.persistent (native,previous)) (invoked : Bool)
    (work : M Platform (RustM (Reply ×beaconcrypt_public_wrapper.beacon.Beacon))) (compatible : Compatible work) :
    finish before index observe invoked <$>((work.run (before.backend.1.world.primitive,[])).run before.backend.2)=
    update before index observe <$>(observed index fallback native (rawBefore before index) invoked <$>
      ((work.run (native.server.world.world.1.primitive,[])).run previous)) := by
  rw [factor before index observe native previous basis invoked work compatible,Functor.map_map]
  congr 1
  funext result
  rcases result with ⟨⟨outcome,reached⟩,next⟩
  cases outcome <;>
    simp only [Function.comp_def,Prod.map,id_eq,finish,observed,RegistrationNativePlatformExtractedSdkOrdinary.pack,update] <;>
    rw [commit_snapshot before native previous basis] <;>rfl

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send_body (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view setup.joint pool self owner world)
    (bytes : Slice U8) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup codec reserve keyView failure erased self bytes) := by
  cases stored:self.state
  case Established control binding manager=>
    obtain ⟨kernel,_completed,sameManager,_phase,_world⟩:=RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established
      view setup.joint pool self owner world related control binding manager stored
    rw [sameManager] at stored
    rw [←RegistrationNativePlatformExtractedSdkOrdinarySendCommon.source setup codec reserve keyView failure erased self control binding kernel stored bytes]
    change Compatible (AdapterPublicOrdinaryKernel.returned self control binding <$>
      RegistrationNativePlatformExtractedSdkOrdinarySendOperands.sample setup codec reserve keyView failure erased control.server_binding.identity_key_id self.identity_key_kid binding.associated_data kernel bytes)
    exact mapped _ _ (send_sample setup codec reserve keyView failure erased control.server_binding.identity_key_id self.identity_key_kid binding.associated_data kernel bytes)
  all_goals
    have idle : AdapterPublicOrdinaryBeacon.Inactive self :=by simp only [AdapterPublicOrdinaryBeacon.Inactive,stored]
    rw [RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.send setup codec reserve keyView failure erased self idle bytes]
    exact pure_compatible _

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive_body (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view setup.joint pool self owner world)
    (bytes : Slice U8) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup codec reserve keyView failure erased self bytes) := by
  cases stored:self.state
  case Established control binding manager=>
    obtain ⟨kernel,_completed,sameManager,_phase,_world⟩:=RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established
      view setup.joint pool self owner world related control binding manager stored
    rw [sameManager] at stored
    rw [←RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveSource.source setup codec reserve keyView failure erased self control binding kernel stored bytes]
    change Compatible (AdapterPublicOrdinaryKernel.returned self control binding <$>
      RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup codec erased.bytes kernel control.server_binding.identity_key_id binding.associated_data bytes)
    exact mapped _ _ (receive_sample setup codec erased.bytes kernel control.server_binding.identity_key_id binding.associated_data bytes)
  all_goals
    have idle : AdapterPublicOrdinaryBeacon.Inactive self :=by simp only [AdapterPublicOrdinaryBeacon.Inactive,stored]
    rw [RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.receive setup codec reserve keyView failure erased self idle bytes]
    exact pure_compatible _

noncomputable def send (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (before : Store n KemSK R Platform) (index : Nat) (bytes : Slice U8) :
    ProbComp (RustM (Option RawCtxSourceSend.Encrypted ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform)) :=
  match before.beacons index with
  | none=>pure (.ok (none,before),before.backend)
  | some self=>finish before index RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply false <$>
    (((RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes).run
      (before.backend.1.world.primitive,[])).run before.backend.2)

noncomputable def receive (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (before : Store n KemSK R Platform) (index : Nat) (bytes : Slice U8) :
    ProbComp (RustM (Option RawCtxWholeOwner.Decrypted ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform)) :=
  match before.beacons index with
  | none=>pure (.ok (none,before),before.backend)
  | some self=>finish before index RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply true <$>
    (((RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes).run
      (before.backend.1.world.primitive,[])).run before.backend.2)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] primitives [FrameDispatchFallback.Operations] in
def observedPacket (index : Nat) (fallback : beaconcrypt_public_wrapper.beacon.Beacon)
    (packet : RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.beacon.Beacon Reply
      (RegistrationNativeExperiment.State n KemSK mlSource) Platform) :=
  let self:=match packet.outcome with | .ok word=>word.2 | _=>fallback
  (packet.outcome,(RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.packet packet index self).committed)

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send_source (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (selected : current.1.beacons[index]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons index=some self) (bytes : Slice U8) :
    send setup reserve keyView failure erased (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index bytes=
      update (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>
        (observedPacket index self <$>RegistrationNativePlatformExtractedSdkOrdinary.run
          (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes)
          current.1 current.2 (current.1.server.world.world.1.ownerRaw index) false) := by
  have found:=before.beacons index
  rw [selected] at found
  obtain ⟨actual,sourceFound,related⟩:=found
  have same : actual=self :=Option.some.inj (sourceFound.symm.trans sourceSelected)
  subst actual
  have compatible:=send_body setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
    view current.1.pool self owner current.1.server.world.world.1.owners[owner.worldOwner]? related bytes
  have fact:=observed_factor (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index self RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply
    current.1 current.2 before.backend false
    (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes) compatible
  have count : rawBefore (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index=current.1.server.world.world.1.ownerRaw index :=
    congrArg (fun value=>value.1.world.ownerRaw index) before.backend
  rw [count] at fact
  unfold send
  change (match before.objects.beacons index with
    | none=>_
    | some object=>_) =_
  rw [sourceSelected]
  simpa only [RegistrationNativePlatformExtractedSdkOrdinary.run,Functor.map_map,observed,observedPacket,
    rawBefore,RegistrationNativePlatformPublicAdapterStore.erase,RegistrationNativePlatformSdkReification.persistent,
    RegistrationNativePlatformSdkReification.backend,RegistrationNativePlatformSdkReification.worldBackend] using fact

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive_source (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (selected : current.1.beacons[index]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons index=some self) (bytes : Slice U8) :
    receive setup reserve keyView failure erased (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index bytes=
      update (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>
        (observedPacket index self <$>RegistrationNativePlatformExtractedSdkOrdinary.run
          (RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes)
          current.1 current.2 (current.1.server.world.world.1.ownerRaw index) true) := by
  have found:=before.beacons index
  rw [selected] at found
  obtain ⟨actual,sourceFound,related⟩:=found
  have same : actual=self :=Option.some.inj (sourceFound.symm.trans sourceSelected)
  subst actual
  have compatible:=receive_body setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
    view current.1.pool self owner current.1.server.world.world.1.owners[owner.worldOwner]? related bytes
  have fact:=observed_factor (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index self RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply
    current.1 current.2 before.backend true
    (RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes) compatible
  have count : rawBefore (RegistrationNativePlatformPublicAdapterStore.erase before.objects) index=current.1.server.world.world.1.ownerRaw index :=
    congrArg (fun value=>value.1.world.ownerRaw index) before.backend
  rw [count] at fact
  unfold receive
  change (match before.objects.beacons index with
    | none=>_
    | some object=>_) =_
  rw [sourceSelected]
  simpa only [RegistrationNativePlatformExtractedSdkOrdinary.run,Functor.map_map,observed,observedPacket,
    rawBefore,RegistrationNativePlatformPublicAdapterStore.erase,RegistrationNativePlatformSdkReification.persistent,
    RegistrationNativePlatformSdkReification.backend,RegistrationNativePlatformSdkReification.worldBackend] using fact

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.commit_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.commit_snapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.observed_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.observed_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive_source
