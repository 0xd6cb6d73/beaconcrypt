-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerStored
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySampleReification
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
/-! Complete ordinary Server SDK bodies execute on actual source objects and the physical primitive/platform backend. The raw runner keeps failure or divergence terminal, without constructing a next Self, and retains the reached backend separately. Its reached normal law and exact attached-query erasure are derived from the same concrete StrongCarrier dispatch, individual map/primitive contracts, actual source marginals, returned-object updates and administrative-only primitive reification. No caller source diagram or whole-operation factor is assumed. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (M State)
open RegistrationNativePlatformSdkOrdinarySendReification (Compatible)
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

open RegistrationNativePlatformSdkOrdinarySampleReification (send_sample received receive_sample)

omit material platform ed primitives [FrameDispatchFallback.Operations] in
def rawBefore (before : Store n KemSK R Platform) : Nat :=
  (before.backend.1.world.server.map (fun records=>records.records.rawAttempts)).getD 0

omit material platform ed primitives [FrameDispatchFallback.Operations] in
def rawAfter (before : Store n KemSK R Platform) (invoked : Bool) : Nat :=rawBefore before+if invoked then 1 else 0

omit primitives [FrameDispatchFallback.Operations] in
def commit (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Store n KemSK R Platform) (self : beaconcrypt_public_wrapper.server.Server)
    (tag : PqxdhDeploymentInterface.FrameTag) (invoked : Bool) (reached : State) (next : Platform) :
    RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform :=
  ({before.backend.1 with world := (PqxdhRecordLiftWorld.produce tag reached.2 {before.backend.1.world with server := some (AdapterPublicOrdinaryServerReifier.server view views self (rawAfter before invoked)), primitive := primitive reached.1})},next)

omit material platform ed primitives [FrameDispatchFallback.Operations] in
def terminal (before : Store n KemSK R Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (invoked : Bool) (reached : State) (next : Platform) :
    RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform :=
  ({before.backend.1 with world := (PqxdhRecordLiftWorld.produce tag reached.2 {before.backend.1.world with server := before.backend.1.world.server.map (fun records=>{records with records:={records.records with rawAttempts:=rawAfter before invoked}}), primitive := primitive reached.1})},next)

omit primitives [FrameDispatchFallback.Operations] in
def finish (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Store n KemSK R Platform) (observe : Reply →PublicReply)
    (tag : PqxdhDeploymentInterface.FrameTag) (invoked : Bool)
    (reached : ((RustM (Reply ×beaconcrypt_public_wrapper.server.Server) ×State) ×Platform)) :
    RustM (PublicReply ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) :=
  match reached.1.1 with
  | .ok word=>
      let backend:=commit view views before word.2 tag invoked reached.1.2 reached.2
      (.ok (observe word.1,RegistrationNativePlatformPublicAdapterStore.server before word.2 backend),backend)
  | .fail error=>(.fail error,terminal before tag invoked reached.1.2 reached.2)
  | .div=>(.div,terminal before tag invoked reached.1.2 reached.2)

omit primitives [FrameDispatchFallback.Operations] in
theorem commit_snapshot (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Store n KemSK R Platform) (native : RegistrationNativeExperiment.State n KemSK mlSource) (previous : Platform)
    (basis : before.backend=RegistrationNativePlatformSdkReification.persistent (native,previous))
    (self : beaconcrypt_public_wrapper.server.Server) (tag : PqxdhDeploymentInterface.FrameTag) (invoked : Bool)
    (reached : State) (next : Platform) :
    commit view views before self tag invoked (journal reached) next=
      RegistrationNativePlatformSdkReification.persistent
        (({returned := self, raw := (RegistrationNativePlatformOrdinaryExperiment.replaceWorld native {native.server.world.world.1 with primitive:=reached.1},next), tag := tag, frames := reached.2, rawBefore := rawBefore before, rawInvoked := invoked} :RegistrationNativePlatformSdkOrdinarySnapshot.Server n KemSK Platform mlSource).committed view views) := by
  have backendEq:=congrArg Prod.fst basis
  unfold commit
  rw [backendEq]
  simp only [RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
    RegistrationNativePlatformSdkReification.worldBackend,RegistrationNativePlatformSdkOrdinarySnapshot.Server.committed,
    RegistrationNativePlatformSdkOrdinarySnapshot.Server.world,RegistrationNativePlatformSdkOrdinarySnapshot.Server.rawAfter,
    RegistrationNativePlatformOrdinaryExperiment.replaceWorld,PqxdhRecordLiftWorld.produce,journal,primitive,
    rawAfter,Function.update_idem]

omit primitives [FrameDispatchFallback.Operations] in
theorem factor (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Store n KemSK R Platform) (observe : Reply →PublicReply)
    (native : RegistrationNativeExperiment.State n KemSK mlSource) (previous : Platform)
    (basis : before.backend=RegistrationNativePlatformSdkReification.persistent (native,previous))
    (tag : PqxdhDeploymentInterface.FrameTag) (invoked : Bool)
    (work : M Platform (RustM (Reply ×beaconcrypt_public_wrapper.server.Server))) (compatible : Compatible work) :
    finish view views before observe tag invoked <$>
      ((work.run (before.backend.1.world.primitive,[])).run before.backend.2)=
    (finish view views before observe tag invoked ∘Prod.map (Prod.map id journal) id) <$>
      ((work.run (native.server.world.world.1.primitive,[])).run previous) := by
  have primitiveEq : before.backend.1.world.primitive=primitive native.server.world.world.1.primitive := by
    rw [basis]
    rfl
  have platformEq : before.backend.2=previous := congrArg Prod.snd basis
  have core:=congrArg (fun value=>value.run previous) (compatible (native.server.world.world.1.primitive,[]))
  rw [StateT.run_map] at core
  have lifted:=congrArg (fun distribution=>finish view views before observe tag invoked <$>distribution) core
  simp only [Functor.map_map] at lifted
  rw [primitiveEq,platformEq]
  exact lifted.symm

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]

noncomputable def send (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Store n KemSK R Platform) (bytes : Slice U8) (key : U64) :
    ProbComp (RustM (Option RawCtxSourceSend.Encrypted ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform)) :=
  finish view views before RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply (PqxdhDeploymentNative.serverTag (.inl ([],key))) false <$>
    (((RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.server bytes key).run
      (before.backend.1.world.primitive,[])).run before.backend.2)

noncomputable def receive (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Store n KemSK R Platform) (bytes : Slice U8) :
    ProbComp (RustM (Option RawCtxWholeOwner.Decrypted ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform)) :=
  finish view views before RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply (PqxdhDeploymentNative.serverTag (.inr [])) true <$>
    (((RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.server bytes).run
      (before.backend.1.world.primitive,[])).run before.backend.2)

theorem send_body (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (bytes : Slice U8) (key : U64) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes key) := by
  cases selected:views.peer before.objects.server.known_ids key with
  | none=>
      rw [RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_send setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased views before.objects.server bytes key (back key) (get key) (borrow key),selected]
      exact pure_compatible _
  | some remote=>
      cases stored:remote.peer.ratchet.refined.kernel with
      | none=>
          obtain ⟨records,_present,_sender,_identity,related⟩:=before.server.peers
          have missing : records.records.server.peers key=none := by
            rw [←(related key).1,selected]
            simp only [Option.bind_some,peerView,stored,Option.map_none]
          have impossible:true=false := by
            simpa only [selected,missing,Option.isSome_some,Option.isSome_none] using (related key).2
          cases impossible
      | some kernel=>
          rw [←RegistrationNativePlatformExtractedSdkOrdinarySendOperands.source setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased views before.objects.server remote (back key) kernel bytes key selected stored (get key) (borrow key)]
          exact mapped _ _ (send_sample setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased key
            (platform.arcView before.objects.server.identity).identity_key_kid remote.peer.binding.associated_data kernel bytes)

theorem receive_body (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (bytes : Slice U8) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    Compatible (RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes) := by
  cases routed:RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.route (TranscriptAuthParts.absSlice bytes) with
  | none=>
      have refused : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused views before.objects.server bytes := by
        simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused,routed]
      rw [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.source_none setup reserve keyView failure erased views before.objects.server bytes refused back get borrow]
      exact pure_compatible _
  | some key=>
      cases selected:views.peer before.objects.server.known_ids key with
      | none=>
          have refused : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused views before.objects.server bytes := by
            simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused,routed,selected]
          rw [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.source_none setup reserve keyView failure erased views before.objects.server bytes refused back get borrow]
          exact pure_compatible _
      | some remote=>
          cases stored:remote.peer.ratchet.refined.kernel with
          | none=>
              obtain ⟨records,_present,_sender,_identity,related⟩:=before.server.peers
              have missing : records.records.server.peers key=none := by
                rw [←(related key).1,selected]
                simp only [Option.bind_some,peerView,stored,Option.map_none]
              have impossible:true=false := by
                simpa only [selected,missing,Option.isSome_some,Option.isSome_none] using (related key).2
              cases impossible
          | some kernel=>
              rw [←RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.source setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased views before.objects.server remote back kernel bytes key routed selected stored get borrow]
              exact mapped _ _ (receive_sample setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) erased.bytes kernel key remote.peer.binding.associated_data bytes)

omit material platform ed primitives [FrameDispatchFallback.Operations] [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
private theorem source_normal {N PublicValue : Type} {Private : N →Type} {model : ProbComp (PublicValue ×N)}
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private model)
    (result : RustM call.step.sourceType ×N) (supported : result∈support call.step.sourceCall) :
    ∃returned,result.1=.ok returned := by
  rw [←call.step.source_exact,support_map] at supported
  obtain ⟨packet,possible,same⟩:=supported
  obtain ⟨returned,normal⟩:=call.normal packet possible
  exact ⟨returned,(congrArg Prod.fst same).symm.trans normal⟩

omit material platform ed primitives [FrameDispatchFallback.Operations] [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
private theorem map_support {T U : Type} (work : ProbComp T) (first second : T →U)
    (same : ∀value,value∈support work→first value=second value) : first <$>work=second <$>work := by
  rw [map_eq_pure_bind,map_eq_pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support work
  intro value supported
  rw [same value supported]

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def observed (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (tag : PqxdhDeploymentInterface.FrameTag) (invoked : Bool)
    (native : RegistrationNativeExperiment.State n KemSK mlSource) (rawCount : Nat)
    (reached : ((RustM (Reply ×beaconcrypt_public_wrapper.server.Server) ×State) ×Platform)) :
    RustM (Reply ×beaconcrypt_public_wrapper.server.Server) ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform) :=
  let packet:=RegistrationNativePlatformExtractedSdkOrdinary.pack native rawCount invoked reached
  (packet.outcome,match packet.outcome with
    | .ok returned=>(RegistrationNativePlatformExtractedSdkOrdinary.serverSnapshot tag packet returned.2).committed view views
    | _=>packet.after)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def update (before : Store n KemSK R Platform) (observe : Reply →PublicReply)
    (result : RustM (Reply ×beaconcrypt_public_wrapper.server.Server) ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform)) :
    RustM (PublicReply ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) :=
  let backend:=RegistrationNativePlatformSdkReification.persistent result.2
  (match result.1 with
    | .ok word=>.ok (observe word.1,RegistrationNativePlatformPublicAdapterStore.server before word.2 backend)
    | .fail error=>.fail error
    | .div=>.div,backend)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem observed_factor (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Store n KemSK R Platform) (observe : Reply →PublicReply)
    (native : RegistrationNativeExperiment.State n KemSK mlSource) (previous : Platform)
    (basis : before.backend=RegistrationNativePlatformSdkReification.persistent (native,previous))
    (tag : PqxdhDeploymentInterface.FrameTag) (invoked : Bool) (rawCount : Nat) (count : rawBefore before=rawCount)
    (work : M Platform (RustM (Reply ×beaconcrypt_public_wrapper.server.Server))) (compatible : Compatible work)
    (normal : ∀result,result∈support ((work.run (native.server.world.world.1.primitive,[])).run previous)→∃returned,result.1.1=.ok returned) :
    finish view views before observe tag invoked <$>
      ((work.run (before.backend.1.world.primitive,[])).run before.backend.2)=
    update before observe <$> (observed view views tag invoked native rawCount <$>
      ((work.run (native.server.world.world.1.primitive,[])).run previous)) := by
  rw [factor view views before observe native previous basis tag invoked work compatible,Functor.map_map]
  apply map_support
  intro result supported
  obtain ⟨word,actual⟩:=normal result supported
  rcases result with ⟨⟨value,reached⟩,next⟩
  dsimp only at actual
  cases actual
  simp only [Function.comp_def,Prod.map,id_eq,finish,observed,RegistrationNativePlatformExtractedSdkOrdinary.pack,update]
  rw [commit_snapshot view views before native previous basis word.2 tag invoked reached next,count]
  rfl

noncomputable def baseOutput {model : ProbComp (PublicReply ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform))}
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential) model)
    (packet : {value //value∈support call.step.sample}) :=
  let next:=RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects
  (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),next),next.backend)

noncomputable def strongOutput {model : ProbComp (PublicReply ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform))}
    (setup : Setup base KemSK) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential) model)
    (packet : {value //value∈support call.step.sample}) :=
  let next:=RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects
  (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),next),next.backend)

omit primitives [FrameDispatchFallback.Operations] [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
private theorem of_base_output {model : ProbComp (PublicReply ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform))}
    (setup : Setup base KemSK) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential) model)
    (coherent : ∀packet : {value //value∈support call.step.sample},
      RegistrationNativePlatformSdkStrongCarrier.OtkPublic (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view
        (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects.beacons)
    (packet : {value //value∈support call.step.sample}) :
    strongOutput setup view views created credential (RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call coherent) packet=
      baseOutput view views setup.joint created credential call packet := by
  unfold strongOutput baseOutput
  rw [RegistrationNativePlatformSdkStrongStep.of_base_base]
  rfl

omit primitives [FrameDispatchFallback.Operations] [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
private theorem of_base_function {model : ProbComp (PublicReply ×(RegistrationNativeExperiment.State n KemSK mlSource ×Platform))}
    (setup : Setup base KemSK) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential) model)
    (coherent : ∀packet : {value //value∈support call.step.sample},
      RegistrationNativePlatformSdkStrongCarrier.OtkPublic (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view
        (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects.beacons) :
    strongOutput setup view views created credential (RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call coherent)=
      baseOutput view views setup.joint created credential call := by
  funext packet
  exact of_base_output setup view views created credential call coherent packet

omit material platform ed primitives [FrameDispatchFallback.Operations] [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
private theorem attached_projection {N T PublicValue : Type} {Private : N →Type} {model : ProbComp (PublicValue ×N)}
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private model)
    (output : {value //value∈support call.step.sample} →T) (change : RustM call.step.sourceType ×N →T)
    (same : ∀packet,output packet=change (call.step.sourceReply packet.val,call.step.sourceState packet.val)) :
    output <$>PFunctor.FreeM.attachSupp call.step.sample=change <$>call.step.sourceCall := by
  have erased:=congrArg (fun work=>(fun packet=>change (call.step.sourceReply packet,call.step.sourceState packet)) <$>work)
    (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
  have closed:=congrArg (fun work=>change <$>work) call.step.source_exact
  simp only [Functor.map_map] at erased closed
  calc
    _ = (fun packet : {value //value∈support call.step.sample}=>change (call.step.sourceReply packet.val,call.step.sourceState packet.val)) <$>
        PFunctor.FreeM.attachSupp call.step.sample := by
      apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp call.step.sample)
      exact funext same
    _ = _ := erased.trans closed

theorem send_live (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (bytes : Slice U8) (key : U64) (remote : Remote ed.PublicKey)
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.live setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views setup.joint created credential
      current before bytes key remote selected kernel stored (back key) (lens key) (get key) (borrow key)
    send setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.objects) bytes key=
      baseOutput view views setup.joint created credential call <$>PFunctor.FreeM.attachSupp call.step.sample := by
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.live setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views setup.joint created credential
    current before bytes key remote selected kernel stored (back key) (lens key) (get key) (borrow key)
  let physical:=RegistrationNativePlatformPublicAdapterStore.erase before.objects
  let fact:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
  let server:=Classical.choose fact
  let work:=RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes key
  have basis : physical.backend=RegistrationNativePlatformSdkReification.persistent current :=before.backend
  have present : current.1.server.world.world.1.server=some server :=(Classical.choose_spec fact).1
  have count : rawBefore physical=server.records.rawAttempts := by
    unfold rawBefore
    rw [basis]
    simp only [RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
      RegistrationNativePlatformSdkReification.worldBackend,present,Option.map_some,Option.getD_some]
  have sourceLaw : call.step.sourceCall=observed view views (PqxdhDeploymentNative.serverTag (.inl ([],key))) false current.1 server.records.rawAttempts <$>
      ((work.run (current.1.server.world.world.1.primitive,[])).run current.2) := by
    dsimp only [call,RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.live]
    simp only [RegistrationNativePlatformExtractedSdkOrdinary.run,Functor.map_map]
    apply congrArg (fun observe=>observe <$>((work.run (current.1.server.world.world.1.primitive,[])).run current.2))
    funext result
    rcases result with ⟨⟨value,reached⟩,next⟩
    cases value <;>rfl
  have normal : ∀result,result∈support ((work.run (current.1.server.world.world.1.primitive,[])).run current.2)→∃returned,result.1.1=.ok returned := by
    intro result supported
    have possible : observed view views (PqxdhDeploymentNative.serverTag (.inl ([],key))) false current.1 server.records.rawAttempts result∈support call.step.sourceCall := by
      rw [sourceLaw,support_map]
      exact ⟨result,supported,rfl⟩
    exact source_normal call _ possible
  calc
    _ = update physical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>call.step.sourceCall := by
      unfold send
      rw [sourceLaw]
      exact observed_factor view views physical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply current.1 current.2 basis
        (PqxdhDeploymentNative.serverTag (.inl ([],key))) false server.records.rawAttempts count work
        (send_body setup reserve keyView failure erased view views created credential current before bytes key back get borrow) normal
    _ = _ := by
      symm
      apply attached_projection call (baseOutput view views setup.joint created credential call)
        (update physical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply)
      intro packet
      have objects:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.objects setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views setup.joint created credential
        current before bytes key remote selected kernel stored (back key) (lens key) (get key) (borrow key) packet
      unfold baseOutput
      rw [objects]
      have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
      unfold update
      rw [actual]
      rfl

theorem receive_live (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (bytes : Slice U8) (key : U64) (remote : Remote ed.PublicKey)
    (routed : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.route (TranscriptAuthParts.absSlice bytes)=some key)
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.live setup reserve length keyView failure erased view views setup.joint created credential
      current before bytes key remote routed selected kernel stored back lens get borrow
    receive setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.objects) bytes=
      baseOutput view views setup.joint created credential call <$>PFunctor.FreeM.attachSupp call.step.sample := by
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.live setup reserve length keyView failure erased view views setup.joint created credential
    current before bytes key remote routed selected kernel stored back lens get borrow
  let physical:=RegistrationNativePlatformPublicAdapterStore.erase before.objects
  let fact:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
  let server:=Classical.choose fact
  let work:=RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes
  have basis : physical.backend=RegistrationNativePlatformSdkReification.persistent current :=before.backend
  have present : current.1.server.world.world.1.server=some server :=(Classical.choose_spec fact).1
  have count : rawBefore physical=server.records.rawAttempts := by
    unfold rawBefore
    rw [basis]
    simp only [RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
      RegistrationNativePlatformSdkReification.worldBackend,present,Option.map_some,Option.getD_some]
  have sourceLaw : call.step.sourceCall=observed view views (PqxdhDeploymentNative.serverTag (.inr [])) true current.1 server.records.rawAttempts <$>
      ((work.run (current.1.server.world.world.1.primitive,[])).run current.2) := by
    dsimp only [call,RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.live]
    simp only [RegistrationNativePlatformExtractedSdkOrdinary.run,Functor.map_map]
    apply congrArg (fun observe=>observe <$>((work.run (current.1.server.world.world.1.primitive,[])).run current.2))
    funext result
    rcases result with ⟨⟨value,reached⟩,next⟩
    cases value <;>rfl
  have normal : ∀result,result∈support ((work.run (current.1.server.world.world.1.primitive,[])).run current.2)→∃returned,result.1.1=.ok returned := by
    intro result supported
    have possible : observed view views (PqxdhDeploymentNative.serverTag (.inr [])) true current.1 server.records.rawAttempts result∈support call.step.sourceCall := by
      rw [sourceLaw,support_map]
      exact ⟨result,supported,rfl⟩
    exact source_normal call _ possible
  calc
    _ = update physical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>call.step.sourceCall := by
      unfold receive
      rw [sourceLaw]
      exact observed_factor view views physical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply current.1 current.2 basis
        (PqxdhDeploymentNative.serverTag (.inr [])) true server.records.rawAttempts count work
        (receive_body setup reserve keyView failure erased view views created credential current before bytes back get borrow) normal
    _ = _ := by
      symm
      apply attached_projection call (baseOutput view views setup.joint created credential call)
        (update physical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply)
      intro packet
      have objects:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.objects setup reserve length keyView failure erased view views setup.joint created credential
        current before bytes key remote routed selected kernel stored back lens get borrow packet
      unfold baseOutput
      rw [objects]
      have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
      unfold update
      rw [actual]
      rfl

omit primitives [FrameDispatchFallback.Operations] [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
private theorem commit_current (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (tag : PqxdhDeploymentInterface.FrameTag) :
    let physical:=RegistrationNativePlatformPublicAdapterStore.erase before.objects
    commit view views physical before.objects.server tag false (physical.backend.1.world.primitive,[]) physical.backend.2=physical.backend := by
  dsimp only
  unfold commit rawAfter rawBefore
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero,PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil]
  rw [RegistrationNativePlatformPublicAdapterServerStored.stored view views joint created credential current before]
  rw [RegistrationNativePlatformPublicAdapterStore.retained view views joint created credential current before]
  simp only [RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
    RegistrationNativePlatformSdkReification.worldBackend,primitive,Function.update_idem]

theorem send_missing (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (bytes : Slice U8) (key : U64) (absent : views.peer before.objects.server.known_ids key=none)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.step setup RegistrationNativeConcreteCodec.wire reserve keyView failure erased route view views setup.joint created credential
      current before bytes key absent (back key) (get key) (borrow key)
    send setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.objects) bytes key=
      baseOutput view views setup.joint created credential call <$>PFunctor.FreeM.attachSupp call.step.sample := by
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.step setup RegistrationNativeConcreteCodec.wire reserve keyView failure erased route view views setup.joint created credential
    current before bytes key absent (back key) (get key) (borrow key)
  let physical:=RegistrationNativePlatformPublicAdapterStore.erase before.objects
  have basis : physical.backend=RegistrationNativePlatformSdkReification.persistent current :=before.backend
  have sourceNone : RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes key=
      pure (.ok (none,before.objects.server)) := by
    rw [RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_send setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased views before.objects.server bytes key (back key) (get key) (borrow key),absent]
    rfl
  have sourceLaw : call.step.sourceCall=pure (.ok (none,before.objects.server),current) := by
    dsimp only [call,RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.step]
    rw [sourceNone]
    simp only [RegistrationNativePlatformExtractedSdkOrdinary.run,StateT.run_pure,map_pure]
    rfl
  have raw : send setup reserve keyView failure erased view views physical bytes key=pure (.ok (none,physical),physical.backend) := by
    have physicalNone : RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased physical.server bytes key=
        pure (.ok (none,physical.server)) := sourceNone
    have nochange : commit view views physical physical.server (PqxdhDeploymentNative.serverTag (.inl ([],key))) false (physical.backend.1.world.primitive,[]) physical.backend.2=physical.backend :=
      commit_current view views setup.joint created credential current before _
    unfold send
    rw [physicalNone]
    simp only [StateT.run_pure,map_pure,finish]
    rw [nochange]
    rfl
  calc
    _ = update physical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>call.step.sourceCall := by
      rw [raw,sourceLaw,map_pure]
      unfold update
      rw [←basis]
      rfl
    _ = _ := by
      symm
      apply attached_projection call (baseOutput view views setup.joint created credential call)
        (update physical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply)
      intro packet
      have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
      have same : RegistrationNativePlatformExtractedSdkPublic.returned call packet=(none,before.objects.server) :=(RustM.ok.inj actual).symm
      unfold baseOutput
      rw [RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.objects]
      unfold update
      rw [actual,same]
      change (.ok (none,physical),physical.backend)=update physical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply (.ok (none,before.objects.server),current)
      unfold update
      rw [←basis]
      rfl

theorem receive_refused (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential current)
    (bytes : Slice U8)
    (refused : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused views before.objects.server bytes)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.step setup reserve keyView failure erased view views setup.joint created credential
      current before bytes refused back get borrow
    receive setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.objects) bytes=
      baseOutput view views setup.joint created credential call <$>PFunctor.FreeM.attachSupp call.step.sample := by
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.step setup reserve keyView failure erased view views setup.joint created credential
    current before bytes refused back get borrow
  let physical:=RegistrationNativePlatformPublicAdapterStore.erase before.objects
  let fact:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
  let server:=Classical.choose fact
  let work:=RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes
  have basis : physical.backend=RegistrationNativePlatformSdkReification.persistent current :=before.backend
  have present : current.1.server.world.world.1.server=some server :=(Classical.choose_spec fact).1
  have count : rawBefore physical=server.records.rawAttempts := by
    unfold rawBefore
    rw [basis]
    simp only [RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
      RegistrationNativePlatformSdkReification.worldBackend,present,Option.map_some,Option.getD_some]
  have sourceLaw : call.step.sourceCall=observed view views (PqxdhDeploymentNative.serverTag (.inr [])) true current.1 server.records.rawAttempts <$>
      ((work.run (current.1.server.world.world.1.primitive,[])).run current.2) := by
    dsimp only [call,RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.step]
    simp only [RegistrationNativePlatformExtractedSdkOrdinary.run,Functor.map_map]
    apply congrArg (fun observe=>observe <$>((work.run (current.1.server.world.world.1.primitive,[])).run current.2))
    funext result
    rcases result with ⟨⟨value,reached⟩,next⟩
    cases value <;>rfl
  have normal : ∀result,result∈support ((work.run (current.1.server.world.world.1.primitive,[])).run current.2)→∃returned,result.1.1=.ok returned := by
    intro result supported
    have possible : observed view views (PqxdhDeploymentNative.serverTag (.inr [])) true current.1 server.records.rawAttempts result∈support call.step.sourceCall := by
      rw [sourceLaw,support_map]
      exact ⟨result,supported,rfl⟩
    exact source_normal call _ possible
  calc
    _ = update physical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>call.step.sourceCall := by
      unfold receive
      rw [sourceLaw]
      exact observed_factor view views physical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply current.1 current.2 basis
        (PqxdhDeploymentNative.serverTag (.inr [])) true server.records.rawAttempts count work
        (receive_body setup reserve keyView failure erased view views created credential current before bytes back get borrow) normal
    _ = _ := by
      symm
      apply attached_projection call (baseOutput view views setup.joint created credential call)
        (update physical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply)
      intro packet
      have objects:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.objects setup reserve keyView failure erased view views setup.joint created credential
        current before bytes refused back get borrow packet
      unfold baseOutput
      rw [objects]
      have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
      have same : RegistrationNativePlatformExtractedSdkPublic.returned call packet=(none,before.objects.server) :=(RustM.ok.inj actual).symm
      unfold update
      rw [actual,same]
      rfl

open RegistrationNativePlatformSdkDependentCases (rec_none rec_some rec_apply)

theorem send_query (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (key : U64) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch.step setup reserve length keyView converted failure erased route view views created credential
      current before bytes key back lens get borrow
    send setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) bytes key=
      strongOutput setup view views created credential call <$>PFunctor.FreeM.attachSupp call.step.sample := by
  cases selected:views.peer before.base.objects.server.known_ids key with
  | none=>
      have leaf:=send_missing setup reserve keyView failure erased route view views created credential current before.base bytes key selected back get borrow
      dsimp only [RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch.step]
      rw [rec_none _ _ _ selected]
      erw [rec_apply _ _ _ selected]
      rw [of_base_function]
      exact leaf
  | some remote=>
      cases stored:remote.peer.ratchet.refined.kernel with
      | none=>
          obtain ⟨records,_present,_sender,_identity,related⟩:=before.base.server.peers
          have missing : records.records.server.peers key=none := by
            rw [←(related key).1,selected]
            simp only [Option.bind_some,peerView,stored,Option.map_none]
          have impossible:true=false := by
            simpa only [selected,missing,Option.isSome_some,Option.isSome_none] using (related key).2
          cases impossible
      | some kernel=>
          have leaf:=send_live setup reserve length keyView converted failure erased route view views created credential current before.base bytes key remote selected kernel stored back lens get borrow
          dsimp only [RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch.step]
          rw [rec_some _ _ _ remote selected]
          erw [rec_apply _ _ _ selected]
          rw [rec_some _ _ _ kernel stored]
          erw [rec_apply _ _ _ stored]
          rw [of_base_function]
          exact leaf

theorem receive_query (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step setup reserve length keyView failure erased view views created credential
      current before bytes back lens get borrow
    receive setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) bytes=
      strongOutput setup view views created credential call <$>PFunctor.FreeM.attachSupp call.step.sample := by
  cases routed:RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.route (TranscriptAuthParts.absSlice bytes) with
  | none=>
      have refused : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused views before.base.objects.server bytes := by
        simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused,routed]
      have leaf:=receive_refused setup reserve keyView failure erased view views created credential current before.base bytes refused back get borrow
      dsimp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step]
      rw [rec_none _ _ _ routed]
      erw [rec_apply _ _ _ routed]
      rw [of_base_function]
      exact leaf
  | some key=>
      cases selected:views.peer before.base.objects.server.known_ids key with
      | none=>
          have refused : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused views before.base.objects.server bytes := by
            simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused,routed,selected]
          have leaf:=receive_refused setup reserve keyView failure erased view views created credential current before.base bytes refused back get borrow
          dsimp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step]
          rw [rec_some _ _ _ key routed]
          erw [rec_apply _ _ _ routed]
          rw [rec_none _ _ _ selected]
          erw [rec_apply _ _ _ selected]
          rw [of_base_function]
          exact leaf
      | some remote=>
          cases stored:remote.peer.ratchet.refined.kernel with
          | none=>
              obtain ⟨records,_present,_sender,_identity,related⟩:=before.base.server.peers
              have missing : records.records.server.peers key=none := by
                rw [←(related key).1,selected]
                simp only [Option.bind_some,peerView,stored,Option.map_none]
              have impossible:true=false := by
                simpa only [selected,missing,Option.isSome_some,Option.isSome_none] using (related key).2
              cases impossible
          | some kernel=>
              have leaf:=receive_live setup reserve length keyView failure erased view views created credential current before.base bytes key remote routed selected kernel stored back lens get borrow
              dsimp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step]
              rw [rec_some _ _ _ key routed]
              erw [rec_apply _ _ _ routed]
              rw [rec_some _ _ _ remote selected]
              erw [rec_apply _ _ _ selected]
              rw [rec_some _ _ _ kernel stored]
              erw [rec_apply _ _ _ stored]
              rw [of_base_function]
              exact leaf

theorem send_normal (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (key : U64) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target))
    (result : RustM (Option RawCtxSourceSend.Encrypted ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform))
    (supported : result∈support (send setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) bytes key)) :
    ∃reply next,result=(.ok (reply,next),next.backend) := by
  rw [send_query setup reserve length keyView converted failure erased route view views created credential current before bytes key back lens get borrow,support_map] at supported
  obtain ⟨packet,_possible,same⟩:=supported
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch.step setup reserve length keyView converted failure erased route view views created credential current before bytes key back lens get borrow
  exact ⟨call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
    RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects,same.symm⟩

theorem receive_normal (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target))
    (result : RustM (Option RawCtxWholeOwner.Decrypted ×Store n KemSK R Platform) ×(RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform))
    (supported : result∈support (receive setup reserve keyView failure erased view views (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) bytes)) :
    ∃reply next,result=(.ok (reply,next),next.backend) := by
  rw [receive_query setup reserve length keyView failure erased view views created credential current before bytes back lens get borrow,support_map] at supported
  obtain ⟨packet,_possible,same⟩:=supported
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step setup reserve length keyView failure erased view views created credential current before bytes back lens get borrow
  exact ⟨call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
    RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects,same.symm⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.commit_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.commit_snapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_refused

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive_normal
