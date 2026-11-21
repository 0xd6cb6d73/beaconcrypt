-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
open RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun (Sample runner source native observed observe)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView)
variable (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
variable (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
variable (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (credential : RegistrationNativeMldsa.Credential mlSource)

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem apply_pure {S A : Type} {m : Type →Type} [Monad m] (value : A) (state : S) :
    (pure value :StateT S m A) state=pure (value,state) := rfl

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem native_none (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (absent : views.peer before.objects.server.known_ids key=none) :
    (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route
      (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))) mlSource).run current.1).run current.2=
      pure ((none,current.1),current.2) := by
  obtain ⟨server,present,matched⟩:=AdapterPublicOrdinaryServerReifier.related view views created credential
    before.objects.server current.1.server before.server
  have missing : server.records.server.peers key=none := by
    rw [←matched]
    change (views.peer before.objects.server.known_ids key).bind peerView=none
    rw [absent]
    rfl
  simp only [RegistrationNativePlatformOrdinaryExperiment.record,StateT.run,RegistrationNativePlatformOrdinaryExperiment.world,
    RegistrationNativePlatformOrdinaryWorld.guarded,CborRecordWorldClient.refusal,CborRecordWorldCursor.worldShell,
    present,Option.map_some,missing,Option.map_none,RegistrationNativePlatformOrdinaryWorld.handler,
    RegistrationNativePlatformOrdinaryWorld.serverStep,MldsaServerRouting.handler,MldsaServerRouting.send,
    PqxdhDeploymentNative.logged_pure,simulateQ_pure,apply_pure,pure_bind,map_pure]
  simp only [PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil,←present]
  rfl

noncomputable def step (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (absent : views.peer before.objects.server.known_ids key=none)
    (back : Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key,back)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (Carrier (R:=R) view views joint created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route
          (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))) mlSource).run current.1).run current.2) := by
  have sourceNone : RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      before.objects.server bytes key=pure (.ok (none,before.objects.server)) := by
    rw [RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_send setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased views before.objects.server bytes key back get borrow,absent]
    rfl
  refine {
    step := {
      Packet := PUnit
      sample := pure PUnit.unit
      sourceType := Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server
      sourceReply := fun _=>.ok (none,before.objects.server)
      sourceState := fun _=>current
      sourceCall := (fun packet=>(packet.outcome,packet.after)) <$>
        RegistrationNativePlatformExtractedSdkOrdinary.run
          (RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased before.objects.server bytes key)
          current.1 current.2 0 false
      source_exact := ?_
      native := fun _=>(none,current)
      native_exact := ?_
      store := fun _ _=>before }
    observe := observe
    normal := fun _ _=>⟨_,rfl⟩
    reply := ?_ }
  · rw [sourceNone]
    simp only [RegistrationNativePlatformExtractedSdkOrdinary.run,StateT.run_pure,map_pure]
    rfl
  · rw [native_none setup wire reserve route view views joint created credential current before bytes key absent]
    simp only [map_pure]
  · intro packet supported returned actual
    cases RustM.ok.inj actual
    rfl

theorem objects (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (absent : views.peer before.objects.server.known_ids key=none)
    (back : Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key,back))
    (packet : {value //value∈support (step setup wire reserve keyView failure erased route view views joint created credential current before bytes key absent back get borrow).step.sample}) :
    (RegistrationNativePlatformExtractedSdkPublic.store (step setup wire reserve keyView failure erased route view views joint created credential current before bytes key absent back get borrow) packet).objects=before.objects := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.native_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.native_none

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.objects
