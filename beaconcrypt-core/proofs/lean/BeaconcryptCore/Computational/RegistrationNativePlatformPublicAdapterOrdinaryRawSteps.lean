-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconNormal
/-! Four ordinary callbacks use the existing concrete SDK source factories at the unchanged raw extracted model. The source Slice operands and production sender route remain exact. Native model transport is derived from the actual extracted record-source theorem; physical marginals retain actual source objects and erase only the indexed observation transcript. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw strongPhysical)
open RegistrationNativePlatformPublicAdapterStore (Store erase)
variable {n : Nat} {I KemSK R P E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (reserveRegistration reservePeer : StateT P ProbComp Bool)
variable (reserveFrame : Nat → StateT P ProbComp (core.result.Result Unit E))
variable (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
variable (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
variable (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "wire" => RegistrationNativeConcreteCodec.wire
local notation "route" => RegistrationNativePlatformPublicAdapterRouting.route

noncomputable def model (query : RegistrationNativeInterface.Spec.Domain) (current : Native × P) :
    ProbComp (RegistrationNativeInterface.Spec.Range query × (Native × P)) :=
  RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((RegistrationNativePlatformPublicAdapterRawModel.raw setup checks representation created credential keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run current.1).run current.2)

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private noncomputable def cast {N Reply : Type} {Private : N → Type} {left right : ProbComp (Reply × N)}
    (same : left=right) (call : TotalStep Private left) : TotalStep Private right := same ▸ call

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem raw_cast {N Reply : Type} {Private : N → Type} {left right : ProbComp (Reply × N)}
    (same : left=right) (call : TotalStep Private left) (physical : ∀current,Private current → Store n KemSK R P) :
    raw physical (cast same call)=raw physical call := by
  cases same
  rfl

noncomputable def physical (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) : Store n KemSK R P :=
  RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (erase before.base.objects)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem raw_normalize {N Reply : Type} {Private : N → Type} {target : ProbComp (Reply × N)}
    (call : TotalStep Private target) (project : ∀current,Private current → Store n KemSK R P) :
    raw (fun current before => RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (project current before)) call =
      RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$> raw project call := by
  unfold raw
  conv_rhs => erw [Functor.map_map]
  rfl

noncomputable def serverSend (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (key : U64) (back : U64 → Option (Remote ed.PublicKey) → PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (model setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (.inr (.serverSend key (TranscriptAuthParts.absSlice bytes))) current) := by
  let call := RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch.step setup reserveFrame sealLength keyView converted failure erased route view views created credential current before bytes key back lens get borrow
  refine cast ?_ call
  unfold model
  rw [RegistrationNativePlatformPublicAdapterRawModel.server_send,
    RegistrationNativePlatformExtractedExperiment.record_source setup wire reserveFrame keyView failure erased route _ mlSource sealLength openLength converted]
  rfl

noncomputable def serverReceive (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (back : U64 → Option (Remote ed.PublicKey) → PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (model setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (.inr (.serverRaw (TranscriptAuthParts.absSlice bytes))) current) := by
  let call := RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step setup reserveFrame openLength keyView failure erased view views created credential current before bytes back lens get borrow
  refine cast ?_ call
  unfold model
  rw [RegistrationNativePlatformPublicAdapterRawModel.server_receive,
    RegistrationNativePlatformExtractedExperiment.record_source setup wire reserveFrame keyView failure erased route _ mlSource sealLength openLength converted]
  rfl

noncomputable def beaconSend (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (index : Nat) (bytes : Slice U8) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (model setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (.inr (.beaconSend index (TranscriptAuthParts.absSlice bytes))) current) := by
  let call := RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send setup reserveFrame sealLength keyView converted failure erased route view views created credential current before index bytes
  refine cast ?_ call
  unfold model
  rw [RegistrationNativePlatformPublicAdapterRawModel.beacon_send,
    RegistrationNativePlatformExtractedExperiment.record_source setup wire reserveFrame keyView failure erased route _ mlSource sealLength openLength converted]
  rfl

noncomputable def beaconReceive (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (index : Nat) (bytes : Slice U8) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (model setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (.inr (.beaconRaw index (TranscriptAuthParts.absSlice bytes))) current) := by
  let call := RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive setup reserveFrame openLength keyView failure erased route view views created credential current before index bytes
  refine cast ?_ call
  unfold model
  rw [RegistrationNativePlatformPublicAdapterRawModel.beacon_receive,
    RegistrationNativePlatformExtractedExperiment.record_source setup wire reserveFrame keyView failure erased route _ mlSource sealLength openLength converted]
  rfl

theorem serverSend_physical (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (key : U64) (back : U64 → Option (Remote ed.PublicKey) → PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    raw (physical setup created credential view views) (serverSend setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer sealLength openLength converted view views current before bytes key back lens get borrow)=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send setup reserveFrame keyView failure erased view views (physical setup created credential view views current before) bytes key := by
  unfold serverSend
  rw [raw_cast]
  change raw (fun current before => RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
    (strongPhysical setup view views created credential current before)) _=_
  rw [raw_normalize]
  have original:=RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_query setup reserveFrame sealLength keyView converted failure erased route view views created credential current before bytes key back lens get borrow
  have erasedLaw : raw (strongPhysical setup view views created credential) _ =
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send setup reserveFrame keyView failure erased view views (erase before.base.objects) bytes key := original.symm
  rw [erasedLaw]
  exact RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_send setup reserveFrame keyView failure erased view views (erase before.base.objects) bytes key

theorem serverReceive_physical (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (back : U64 → Option (Remote ed.PublicKey) → PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    raw (physical setup created credential view views) (serverReceive setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer sealLength openLength converted view views current before bytes back lens get borrow)=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive setup reserveFrame keyView failure erased view views (physical setup created credential view views current before) bytes := by
  unfold serverReceive
  rw [raw_cast]
  change raw (fun current before => RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
    (strongPhysical setup view views created credential current before)) _=_
  rw [raw_normalize]
  have original:=RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_query setup reserveFrame openLength keyView failure erased view views created credential current before bytes back lens get borrow
  have erasedLaw : raw (strongPhysical setup view views created credential) _ =
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive setup reserveFrame keyView failure erased view views (erase before.base.objects) bytes := original.symm
  rw [erasedLaw]
  exact RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_receive setup reserveFrame keyView failure erased view views (erase before.base.objects) bytes

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem beaconSend_physical (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (index : Nat) (bytes : Slice U8) :
    raw (physical setup created credential view views) (beaconSend setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer sealLength openLength converted view views current before index bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup reserveFrame keyView failure erased (physical setup created credential view views current before) index bytes := by
  unfold beaconSend
  rw [raw_cast]
  change raw (fun current before => RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
    (strongPhysical setup view views created credential current before)) _=_
  rw [raw_normalize]
  rw [RegistrationNativePlatformSdkOrdinaryBeaconErasure.send setup reserveFrame sealLength keyView converted failure erased route view views created credential current before index bytes]
  exact RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_send setup reserveFrame keyView failure erased (erase before.base.objects) index bytes

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem beaconReceive_physical (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (index : Nat) (bytes : Slice U8) :
    raw (physical setup created credential view views) (beaconReceive setup checks representation created credential keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer sealLength openLength converted view views current before index bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup reserveFrame keyView failure erased (physical setup created credential view views current before) index bytes := by
  unfold beaconReceive
  rw [raw_cast]
  change raw (fun current before => RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
    (strongPhysical setup view views created credential current before)) _=_
  rw [raw_normalize]
  rw [RegistrationNativePlatformSdkOrdinaryBeaconErasure.receive setup reserveFrame openLength keyView failure erased route view views created credential current before index bytes]
  exact RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_receive setup reserveFrame keyView failure erased (erase before.base.objects) index bytes

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverSend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverReceive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconSend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconReceive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverSend_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverSend_physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverReceive_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverReceive_physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconSend_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconSend_physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconReceive_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconReceive_physical
