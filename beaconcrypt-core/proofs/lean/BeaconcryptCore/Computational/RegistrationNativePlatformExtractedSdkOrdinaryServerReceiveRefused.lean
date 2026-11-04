-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
open RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun (Sample runner source native observed observe)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView)
variable (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
open RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep (route)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
variable (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : RegistrationNativeMldsa.Credential mlSource)

def Refused (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) : Prop :=
  match route (TranscriptAuthParts.absSlice bytes) with
  | none=>True
  | some key=>views.peer self.known_ids key=none

theorem source_none (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8)
    (refused : Refused views self bytes) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids target=pure (views.peer self.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids target=pure (views.peer self.known_ids target,back target)) :
    RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes=
      pure (.ok (none,self)) := by
  let := RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
  rw [RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_receive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased views self bytes back get borrow,
    AdapterPublicOrdinaryServerSender.source]
  change ((do
    let key←(pure (route (TranscriptAuthParts.absSlice bytes)) :AdapterPublicWrapperRustT.RustT (RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) _)
    match key with
    | none=>pure (none,self)
    | some key=>RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receiveAt self bytes key (views.peer self.known_ids key) (back key))).run=_
  simp only [pure_bind]
  cases routed:route (TranscriptAuthParts.absSlice bytes) with
  | none=>rfl
  | some key=>
      simp only [Refused,routed] at refused
      dsimp only
      rw [refused]
      rfl

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem apply_pure {S A : Type} {m : Type →Type} [Monad m] (value : A) (state : S) :
    (pure value :StateT S m A) state=pure (value,state) := rfl

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem native_none (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (refused : Refused views before.objects.server bytes)
    (server : PqxdhRecordLiftWorld.Server) (present : current.1.server.world.world.1.server=some server)
    (matched : AdapterPublicOrdinaryServerReifier.server view views before.objects.server server.records.rawAttempts=server) :
    (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
      (.inl (.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2=
      (let after:=(RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.snapshot current.1 before.objects.server
        current.1.server.world.world.1.primitive [] current.2 (PqxdhDeploymentNative.serverTag (.inr [])) server.records.rawAttempts true).committed view views
       pure ((none,after.1),after.2)) := by
  have shifted : AdapterPublicOrdinaryServerReifier.server view views before.objects.server (server.records.rawAttempts+1)=
      {server with records:={server.records with rawAttempts:=server.records.rawAttempts+1}} := by
    conv_rhs=>rw [←matched]
    rfl
  have missing : (match route (TranscriptAuthParts.absSlice bytes) with
      | none=>True
      | some key=>server.records.server.peers key=none) := by
    cases routeEq:route (TranscriptAuthParts.absSlice bytes) with
    | none=>trivial
    | some key=>
        simp only [Refused,routeEq] at refused
        rw [←matched]
        change (views.peer before.objects.server.known_ids key).bind peerView=none
        rw [refused]
        rfl
  have returned : MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _=>server.sender) route
      (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (.inr (TranscriptAuthParts.absSlice bytes)) server.records =
      pure (.None,{server.records with rawAttempts:=server.records.rawAttempts+1}) := by
    simp only [MldsaServerRouting.handler,MldsaServerRouting.receive]
    cases routed:route (TranscriptAuthParts.absSlice bytes) with
    | none=>rfl
    | some key=>
        simp only [routed] at missing
        dsimp only
        rw [missing]
  simp only [RegistrationNativePlatformOrdinaryExperiment.record,StateT.run,RegistrationNativePlatformOrdinaryExperiment.world,
    RegistrationNativePlatformOrdinaryWorld.guarded,CborRecordWorldClient.refusal,
    RegistrationNativePlatformOrdinaryWorld.handler,RegistrationNativePlatformOrdinaryWorld.serverStep,present]
  rw [returned,PqxdhDeploymentNative.logged_pure,simulateQ_pure]
  simp only [apply_pure,pure_bind,map_pure,RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.snapshot,
    RegistrationNativePlatformSdkOrdinarySnapshot.Server.committed,RegistrationNativePlatformSdkOrdinarySnapshot.Server.world,
    RegistrationNativePlatformSdkOrdinarySnapshot.Server.rawAfter,ite_true,shifted,PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil]
  rfl

noncomputable def step (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (refused : Refused views before.objects.server bytes)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (Carrier (R:=R) view views joint created credential)
      ((fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
          (.inl (.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
  let fact:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
  let server:=Classical.choose fact
  have present:= (Classical.choose_spec fact).1
  have matched : AdapterPublicOrdinaryServerReifier.server view views before.objects.server server.records.rawAttempts=server := (Classical.choose_spec fact).2
  let snapshot:=RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.snapshot current.1 before.objects.server
    current.1.server.world.world.1.primitive [] current.2 (PqxdhDeploymentNative.serverTag (.inr [])) server.records.rawAttempts true
  refine {
    step := {
      Packet := PUnit
      sample := pure PUnit.unit
      sourceType := Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server
      sourceReply := fun _=>.ok (none,before.objects.server)
      sourceState := fun _=>snapshot.committed view views
      sourceCall := observed (0#u64) view views <$>RegistrationNativePlatformExtractedSdkOrdinary.run
        (RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes)
        current.1 current.2 server.records.rawAttempts true
      source_exact := ?_
      native := fun _=>(none,snapshot.committed view views)
      native_exact := ?_
      store := fun _ _=>RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.put view views joint created credential current before
        current.1.server.world.world.1.primitive [] current.2 (PqxdhDeploymentNative.serverTag (.inr [])) server.records.rawAttempts true }
    observe := observe
    normal := fun _ _=>⟨_,rfl⟩
    reply := ?_ }
  · rw [source_none setup reserve keyView failure erased views before.objects.server bytes refused back get borrow]
    simp only [RegistrationNativePlatformExtractedSdkOrdinary.run,StateT.run_pure,map_pure]
    rfl
  · rw [native_none setup reserve view views joint created credential current before bytes refused server present matched]
    simp only [map_pure]
    rfl
  · intro packet supported returned actual
    cases RustM.ok.inj actual
    rfl

theorem objects (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (refused : Refused views before.objects.server bytes)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target))
    (packet : {value //value∈support (step setup reserve keyView failure erased view views joint created credential current before bytes refused back get borrow).step.sample}) :
    let call:=step setup reserve keyView failure erased view views joint created credential current before bytes refused back get borrow
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects=
      {before.objects with snapshot:=.direct (call.step.sourceState packet.val)} := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.source_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.source_none

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.native_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.native_none

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.objects
