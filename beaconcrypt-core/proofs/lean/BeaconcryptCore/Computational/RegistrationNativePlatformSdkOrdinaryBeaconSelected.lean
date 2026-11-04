-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformPublicAdapterStore (Store erase)
variable {n : Nat} {I KemSK Platform R Reply N E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

noncomputable def raw {Private : N→Type} {model : ProbComp (Reply×N)}
    (physical : ∀current,Private current→Store n KemSK R Platform) (call : TotalStep Private model) :
    ProbComp (RustM (Reply×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK×Platform)) :=
  (fun packet=>
    let next:=physical (call.step.native packet.val).2 (RegistrationNativePlatformExtractedSdkPublic.store call packet)
    (.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),next),next.backend)) <$>
      PFunctor.FreeM.attachSupp call.step.sample

omit material platform ed in
private theorem source_eq {S : Type} {Private : N→Type} {model : ProbComp (Reply×N)}
    (call : TotalStep Private model) (first : {packet //packet∈support call.step.sample}→S)
    (update : RustM call.step.sourceType×N→S)
    (retained : ∀packet,first packet=update (call.step.sourceReply packet.val,call.step.sourceState packet.val)) :
    first <$>PFunctor.FreeM.attachSupp call.step.sample=update <$>call.step.sourceCall := by
  rw [←call.step.source_exact,Functor.map_map]
  have erased:=congrArg (fun work=>(fun packet=>update (call.step.sourceReply packet,call.step.sourceState packet)) <$>work)
    (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
  simp only [Functor.map_map] at erased
  rw [←erased]
  congr 1
  funext packet
  exact retained packet

noncomputable def basePhysical (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : RegistrationNativeExperiment.State n KemSK source×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current) : Store n KemSK R Platform :=erase before.objects

noncomputable def strongPhysical (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : RegistrationNativeExperiment.State n KemSK source×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) : Store n KemSK R Platform :=erase before.base.objects

theorem of_base (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    {model : ProbComp (Reply×(RegistrationNativeExperiment.State n KemSK source×Platform))}
    (call : TotalStep (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential) model)
    (coherent : ∀packet,RegistrationNativePlatformSdkStrongCarrier.OtkPublic
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view
      (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects.beacons) :
    raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call coherent)=
      raw (basePhysical view views setup.joint created credential) call := by
  unfold raw
  congr 1
  funext packet
  simp only [strongPhysical,basePhysical,RegistrationNativePlatformSdkStrongStep.of_base_base]
  rfl
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem active_send (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native ×Platform) (before : Carrier (R:=R) view containers setup.joint created credential current)
    (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : current.1.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons logical=some self)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel))
    (completed : RegistrationBeaconSeed.PublicCompleted) (phase : owner.phase=.established completed)
    (present : current.1.server.world.world.1.owners[owner.worldOwner]?=some
      (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) kernel))
    (bytes : Slice U8) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps.active_send setup wire reserve length keyView converted failure erased route view containers created credential current before logical owner selected self sourceSelected control binding kernel stored completed phase present bytes
    raw (basePhysical view containers setup.joint created credential) call=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>call.step.sourceCall := by
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps.active_send setup wire reserve length keyView converted failure erased route view containers created credential current before logical owner selected self sourceSelected control binding kernel stored completed phase present bytes
  unfold raw
  apply source_eq call
  intro packet
  obtain ⟨⟨final,pubReply⟩,normal⟩:=RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_normal setup (RegistrationNativeWire.ledgerCodec wire) reserve length keyView converted failure erased
      self control binding kernel bytes (current.1.server.world.world.1.primitive,[]) packet.val.1.2 current.2 packet.val.2 packet.val.1.1 packet.property
  have marked:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
  change AdapterPublicOrdinaryKernel.returned self control binding packet.val.1.1=.ok (RegistrationNativePlatformExtractedSdkPublic.returned call packet) at marked
  rw [normal,AdapterPublicOrdinaryKernel.returned_exact] at marked
  have returnedEq : RegistrationNativePlatformExtractedSdkPublic.returned call packet=
      (pubReply,RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.returned self control binding final) :=(RustM.ok.inj marked).symm
  have kept : (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects=
      RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.update before.objects logical owner.worldOwner current.1 self control binding final packet.val := by
    rcases packet with ⟨⟨⟨outcome,after⟩,afterP⟩,supported⟩
    dsimp only at normal
    subst outcome
    rfl
  change (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
      erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects),
    (erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects).backend)=_
  rw [returnedEq,kept]
  have output : call.step.sourceReply packet.val=.ok (pubReply,RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.returned self control binding final) := by
    change AdapterPublicOrdinaryKernel.returned self control binding packet.val.1.1=_
    rw [normal,AdapterPublicOrdinaryKernel.returned_exact]
    rfl
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update,output]
  rfl
omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem active_receive (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native ×Platform) (before : Carrier (R:=R) view containers setup.joint created credential current)
    (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : current.1.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons logical=some self)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel))
    (completed : RegistrationBeaconSeed.PublicCompleted) (phase : owner.phase=.established completed)
    (present : current.1.server.world.world.1.owners[owner.worldOwner]?=some
      (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) kernel))
    (bytes : Slice U8) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveSteps.active_receive setup reserve length keyView failure erased route view containers created credential current before logical owner selected self sourceSelected control binding kernel stored completed phase present bytes
    raw (basePhysical view containers setup.joint created credential) call=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>call.step.sourceCall := by
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveSteps.active_receive setup reserve length keyView failure erased route view containers created credential current before logical owner selected self sourceSelected control binding kernel stored completed phase present bytes
  unfold raw
  apply source_eq call
  intro packet
  obtain ⟨⟨final,pubReply⟩,normal⟩:=RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.normal setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) length erased.bytes
      kernel control.server_binding.identity_key_id binding.associated_data bytes (current.1.server.world.world.1.primitive,[])
      packet.val.1.2 current.2 packet.val.2 packet.val.1.1 packet.property
  have marked:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
  change AdapterPublicOrdinaryKernel.returned self control binding packet.val.1.1=.ok (RegistrationNativePlatformExtractedSdkPublic.returned call packet) at marked
  rw [normal,AdapterPublicOrdinaryKernel.returned_exact] at marked
  have returnedEq : RegistrationNativePlatformExtractedSdkPublic.returned call packet=
      (pubReply,RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeaconReceive.returned self control binding final) :=(RustM.ok.inj marked).symm
  have kept : (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects=
      RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeaconReceive.update before.objects logical owner.worldOwner current.1 self control binding final packet.val := by
    rcases packet with ⟨⟨⟨outcome,after⟩,afterP⟩,supported⟩
    dsimp only at normal
    subst outcome
    rfl
  change (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
      erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects),
    (erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects).backend)=_
  rw [returnedEq,kept]
  have output : call.step.sourceReply packet.val=.ok (pubReply,RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeaconReceive.returned self control binding final) := by
    change AdapterPublicOrdinaryKernel.returned self control binding packet.val.1.1=_
    rw [normal,AdapterPublicOrdinaryKernel.returned_exact]
    rfl
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update,output]
  rfl

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem idle_send (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×Platform) (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (selected : current.1.beacons[logical]?=some owner) (tag : PqxdhRecordLiftInterface.InactivePhase)
    (inactive : current.1.server.world.world.1.owners[owner.worldOwner]?=some (.inactive tag))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (idle : AdapterPublicOrdinaryBeacon.Inactive self) (sourceSelected : before.base.objects.beacons logical=some self) :
    let call:=RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send setup wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag inactive self idle
    raw (strongPhysical setup view views created credential) call=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>call.step.sourceCall := by
  let call:=RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send setup wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag inactive self idle
  unfold raw
  apply source_eq call
  intro packet
  have returnedEq : RegistrationNativePlatformExtractedSdkPublic.returned call packet=(none,self) :=
    (RustM.ok.inj (RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet)).symm
  have kept : (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects=
      {before.base.objects with snapshot:=.direct (RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot current self owner.worldOwner false).committed} :=rfl
  change (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
      erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects),
    (erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects).backend)=_
  rw [returnedEq,kept]
  have unchanged : Function.update before.base.objects.beacons logical (some self)=before.base.objects.beacons :=by
    rw [←sourceSelected,Function.update_eq_self]
  change (RustM.ok (none,_),_)=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update _ _ _
    (.ok (none,self),(RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot current self owner.worldOwner false).committed)
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update,erase,
    RegistrationNativePlatformPublicAdapterStore.beacon,unchanged]
  rfl

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem idle_receive (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×Platform) (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (selected : current.1.beacons[logical]?=some owner) (tag : PqxdhRecordLiftInterface.InactivePhase)
    (inactive : current.1.server.world.world.1.owners[owner.worldOwner]?=some (.inactive tag))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (idle : AdapterPublicOrdinaryBeacon.Inactive self) (sourceSelected : before.base.objects.beacons logical=some self) :
    let call:=RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive setup wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag inactive self idle
    raw (strongPhysical setup view views created credential) call=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>call.step.sourceCall := by
  let call:=RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive setup wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag inactive self idle
  unfold raw
  apply source_eq call
  intro packet
  have returnedEq : RegistrationNativePlatformExtractedSdkPublic.returned call packet=(none,self) :=
    (RustM.ok.inj (RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet)).symm
  have kept : (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects=
      {before.base.objects with snapshot:=.direct (RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot current self owner.worldOwner true).committed} :=rfl
  change (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
      erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects),
    (erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects).backend)=_
  rw [returnedEq,kept]
  have unchanged : Function.update before.base.objects.beacons logical (some self)=before.base.objects.beacons :=by
    rw [←sourceSelected,Function.update_eq_self]
  change (RustM.ok (none,_),_)=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update _ _ _
    (.ok (none,self),(RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot current self owner.worldOwner true).committed)
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update,erase,
    RegistrationNativePlatformPublicAdapterStore.beacon,unchanged]
  rfl

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] primitives [FrameDispatchFallback.Operations] in
theorem missing_send (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×Platform) (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Pqxdh.Bytes) (missing : current.1.beacons[logical]?=none) :
    raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconMissing.send setup wire reserve route view views created credential current before logical bytes missing)=
      pure (.ok ((none :Option RawCtxSourceSend.Encrypted),erase before.base.objects),(erase before.base.objects).backend) :=by
  let call:=RegistrationNativePlatformSdkOrdinaryBeaconMissing.send setup wire reserve route view views created credential current before logical bytes missing
  let result := (RustM.ok ((none :Option RawCtxSourceSend.Encrypted),erase before.base.objects),(erase before.base.objects).backend)
  calc
    raw (strongPhysical setup view views created credential) call=(fun _=>result) <$>call.step.sourceCall :=by
      unfold raw
      apply source_eq call
      intro packet
      have returnedEq : RegistrationNativePlatformExtractedSdkPublic.returned call packet=none :=
        (RustM.ok.inj (RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet)).symm
      change (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
        erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects),
        (erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects).backend)=_
      rw [returnedEq]
      rfl
    _=pure result :=by simp only [call,RegistrationNativePlatformSdkOrdinaryBeaconMissing.send,map_pure]

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] primitives [FrameDispatchFallback.Operations] in
theorem missing_receive (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×Platform) (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Pqxdh.Bytes) (missing : current.1.beacons[logical]?=none) :
    raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive setup wire reserve route view views created credential current before logical bytes missing)=
      pure (.ok ((none :Option RawCtxWholeOwner.Decrypted),erase before.base.objects),(erase before.base.objects).backend) :=by
  let call:=RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive setup wire reserve route view views created credential current before logical bytes missing
  let result := (RustM.ok ((none :Option RawCtxWholeOwner.Decrypted),erase before.base.objects),(erase before.base.objects).backend)
  calc
    raw (strongPhysical setup view views created credential) call=(fun _=>result) <$>call.step.sourceCall :=by
      unfold raw
      apply source_eq call
      intro packet
      have returnedEq : RegistrationNativePlatformExtractedSdkPublic.returned call packet=none :=
        (RustM.ok.inj (RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet)).symm
      change (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
        erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects),
        (erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects).backend)=_
      rw [returnedEq]
      rfl
    _=pure result :=by simp only [call,RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive,map_pure]

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.of_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.of_base

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.active_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.active_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.active_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.active_receive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.idle_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.idle_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.idle_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.idle_receive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.missing_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.missing_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.missing_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected.missing_receive
