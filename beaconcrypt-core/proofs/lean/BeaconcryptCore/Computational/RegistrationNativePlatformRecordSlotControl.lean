-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots
/-! The literal free Protocol controller derives its opaque handle origins from actual query/reply annotations. Source record replies and refused sends cannot change those slot IDs. No concrete primitive or record interpretation is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl
open PqxdhRecordLiftInterface
open PqxdhRecordLiftProtocol (Control ServiceSpec)
open PqxdhRecordLiftWorldCompiler (StoredKernel Owner Phase Server Peer)
open PqxdhRecordLiftWorldProvenance
variable {n : Nat}

def origins (before : Control n) : PqxdhRecordLiftOrigins.Origins n :=
  PqxdhRecordLiftWorldCompiler.origins (PqxdhRecordLiftProtocolHistory.view before)

private theorem kernel_send (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (result : StoredKernel n × Option RawCtxSourceSend.Encrypted)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.kernelSend stored context)) :
    result.1.origin=stored.origin := by
  cases stored <;>
    simp only [PqxdhRecordLiftProtocol.kernelSend,bind_pure_comp,support_map] at supported
  all_goals obtain ⟨inner,_called,rfl⟩ := supported
  all_goals rfl

private theorem kernel_receive (stored : StoredKernel n) (sequence : U64) (context : RawCtxWholeOwner.OpenContext)
    (result : StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.kernelReceive stored sequence context)) :
    result.1.origin=stored.origin := by
  cases stored <;>
    simp only [PqxdhRecordLiftProtocol.kernelReceive,bind_pure_comp,support_map] at supported
  all_goals obtain ⟨inner,_called,rfl⟩ := supported
  all_goals rfl

private theorem owner_send (sender : U64) (plaintext : Pqxdh.Bytes) (owner : Owner n)
    (result : Option RawCtxSourceSend.Encrypted × Owner n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)) :
    result.2.kernel.origin=owner.kernel.origin := by
  unfold PqxdhRecordLiftProtocol.ownerSend at supported
  split at supported
  · obtain rfl := eq_of_mem_support_pure _ supported
    rfl
  · simp only [bind_pure_comp,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact kernel_send owner.kernel _ inner called

private theorem owner_receive (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × Owner n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.ownerReceive decode raw owner)) :
    result.2.kernel.origin=owner.kernel.origin := by
  unfold PqxdhRecordLiftProtocol.ownerReceive at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [bind_pure_comp,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact kernel_receive owner.kernel _ _ inner called
  all_goals obtain rfl := eq_of_mem_support_pure _ supported
  all_goals rfl

private theorem owner_run (tag : PqxdhDeploymentInterface.FrameTag) (sender : U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × Owner n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner)) :
    result.2.kernel.origin=owner.kernel.origin := by
  simp only [PqxdhRecordLiftProtocol.ownerRun,mem_support_bind_iff] at supported
  obtain ⟨inner,called,reply,_published,returned⟩ := supported
  have same : result=inner := eq_of_mem_support_pure _ returned
  subst result
  cases query with
  | inl plaintext => exact owner_send sender plaintext owner inner called
  | inr raw => exact owner_receive decode raw owner inner called

private theorem server_store (before : Control n) (server : Server n) (present : before.server=some server)
    (keyId : U64) (peer : Peer n) (found : server.peers keyId=some peer) (next : StoredKernel n) (raw : Nat)
    (kept : next.origin=peer.kernel.origin) :
    origins {before with server:=some {server with peers:=Function.update server.peers keyId (some {peer with kernel:=next}),rawAttempts:=raw}} = origins before := by
  apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
  · funext target
    by_cases same : target=keyId
    · subst target
      simp only [PqxdhRecordLiftProtocolHistory.view,
        PqxdhRecordLiftProtocol.join,present,Option.bind_some,Function.update_self,found,kept]
    · simp only [PqxdhRecordLiftProtocolHistory.view,
        PqxdhRecordLiftProtocol.join,present,Option.bind_some,Function.update_of_ne same]
  · rfl

private theorem server_raw (before : Control n) (server : Server n) (present : before.server=some server) (raw : Nat) :
    origins {before with server:=some {server with rawAttempts:=raw}}=origins before := by
  simp only [origins,PqxdhRecordLiftWorldCompiler.origins,PqxdhRecordLiftProtocolHistory.view,
    PqxdhRecordLiftProtocol.join,present,Option.bind_some]

/-- Every raw Server send/receive path retains the entire opaque origin map, including failures after kernel advancement. -/
theorem server_step (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (before : Control n)
    (result : RawCtxServerMixed.SourceSpec.Range query × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.serverStep decode route query before)) :
    origins result.2=origins before := by
  cases present : before.server with
  | none =>
    cases query <;> simp only [PqxdhRecordLiftProtocol.serverStep,present] at supported <;>
      obtain rfl := eq_of_mem_support_pure _ supported <;> rfl
  | some server =>
    cases query with
    | inl request =>
      obtain ⟨plaintext,keyId⟩ := request
      cases found : server.peers keyId with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep,present,found] at supported
        obtain rfl := eq_of_mem_support_pure _ supported
        rfl
      | some peer =>
        simp only [PqxdhRecordLiftProtocol.serverStep,present,found,bind_pure_comp,support_map] at supported
        obtain ⟨inner,called,rfl⟩ := supported
        exact server_store before server present keyId peer found _ _ (owner_run _ _ decode (.inl plaintext) _ inner called)
    | inr raw =>
      cases routed : route raw with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep,present,routed] at supported
        obtain rfl := eq_of_mem_support_pure _ supported
        exact server_raw before server present _
      | some keyId =>
        cases found : server.peers keyId with
        | none =>
          simp only [PqxdhRecordLiftProtocol.serverStep,present,routed,found] at supported
          obtain rfl := eq_of_mem_support_pure _ supported
          exact server_raw before server present _
        | some peer =>
          simp only [PqxdhRecordLiftProtocol.serverStep,present,routed,found,bind_pure_comp,support_map] at supported
          obtain ⟨inner,called,rfl⟩ := supported
          exact server_store before server present keyId peer found _ _ (owner_run _ _ decode (.inr raw) _ inner called)

/-- Actual Beacon raw calls preserve installed slot IDs under every parser, phase and service reply. -/
theorem beacon_step (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (before : Control n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.beaconStep decode owner query before)) :
    origins result.2=origins before := by
  cases found : before.owners[owner]? with
  | none =>
    simp only [PqxdhRecordLiftProtocol.beaconStep,found] at supported
    obtain rfl := eq_of_mem_support_pure _ supported
    rfl
  | some phase => cases phase with
    | inactive phase =>
      cases query <;> simp only [PqxdhRecordLiftProtocol.beaconStep,found] at supported <;>
        obtain rfl := eq_of_mem_support_pure _ supported <;> rfl
    | established shell kernel =>
      simp only [PqxdhRecordLiftProtocol.beaconStep,found,bind_pure_comp,support_map] at supported
      obtain ⟨inner,called,rfl⟩ := supported
      exact origins_owner_same (PqxdhRecordLiftProtocolHistory.view before) owner (.established shell kernel)
        (.established shell inner.2.kernel) found (owner_run _ _ decode query _ inner called)
private theorem mark_origins (before : Control n) (role : Role) (ref : KernelRef n) :
    origins (PqxdhRecordLiftProtocol.markUsed before role ref)=origins before := by
  cases ref <;> rfl

private theorem install_server (keyId : U64) (identity : PeerBinding) (ref : KernelRef n)
    (before : Control n) (result : Bool × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.installServer keyId identity ref before)) :
    origins result.2 = if result.1 then
      {origins before with peers:=Function.update (origins before).peers keyId (PqxdhRecordLiftOrigins.origin ref)}
      else origins before := by
  simp only [PqxdhRecordLiftProtocol.installServer] at supported
  cases present : before.server with
  | none =>
    simp only [present] at supported
    obtain rfl := eq_of_mem_support_pure _ supported
    rfl
  | some server =>
    simp only [present] at supported
    split at supported
    · simp only [bind_pure_comp,support_map] at supported
      obtain ⟨stored,called,rfl⟩ := supported
      have resolved := (PqxdhRecordLiftProtocolHistory.resolve_facts .server ref stored called).2
      have marked : (PqxdhRecordLiftProtocol.markUsed before .server ref).server=some server := by
        cases ref <;> exact present
      change PqxdhRecordLiftWorldCompiler.origins {PqxdhRecordLiftProtocolHistory.view (PqxdhRecordLiftProtocol.markUsed before .server ref) with
        server:=some {server with peers:=Function.update server.peers keyId (some ⟨identity,stored⟩)}} = _
      rw [origins_server_store _ server marked]
      change {origins (PqxdhRecordLiftProtocol.markUsed before .server ref) with
        peers:=Function.update (origins (PqxdhRecordLiftProtocol.markUsed before .server ref)).peers keyId stored.origin} =
        {origins before with peers:=Function.update (origins before).peers keyId (PqxdhRecordLiftOrigins.origin ref)}
      rw [mark_origins,resolved]
    · obtain rfl := eq_of_mem_support_pure _ supported
      rfl

private theorem install_beacon (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (before : Control n) (result : Bool × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.installBeacon owner shell ref before)) :
    origins result.2 = if result.1 then
      {origins before with owners:=Function.update (origins before).owners owner (PqxdhRecordLiftOrigins.origin ref)}
      else origins before := by
  simp only [PqxdhRecordLiftProtocol.installBeacon] at supported
  split at supported
  · rename_i admitted
    simp only [bind_pure_comp,support_map] at supported
    obtain ⟨stored,called,rfl⟩ := supported
    have resolved := (PqxdhRecordLiftProtocolHistory.resolve_facts .beacon ref stored called).2
    have marked : (PqxdhRecordLiftProtocol.markUsed before .beacon ref).owners=before.owners := by
      cases ref <;> rfl
    have within : owner < (PqxdhRecordLiftProtocol.markUsed before .beacon ref).owners.length := by
      rw [marked]
      exact (List.getElem?_eq_some_iff.mp admitted.1).1
    have store := origins_owner_store (PqxdhRecordLiftProtocolHistory.view (PqxdhRecordLiftProtocol.markUsed before .beacon ref))
      owner (.established shell stored) within
    change origins {PqxdhRecordLiftProtocol.markUsed before .beacon ref with
      owners:=before.owners.set owner (.established shell stored)} =
      {origins before with owners:=Function.update (origins before).owners owner (PqxdhRecordLiftOrigins.origin ref)}
    rw [← marked]
    change PqxdhRecordLiftWorldCompiler.origins {PqxdhRecordLiftProtocolHistory.view (PqxdhRecordLiftProtocol.markUsed before .beacon ref) with
      owners:=(PqxdhRecordLiftProtocolHistory.view (PqxdhRecordLiftProtocol.markUsed before .beacon ref)).owners.set owner (.established shell stored)} = _
    rw [store]
    change {origins (PqxdhRecordLiftProtocol.markUsed before .beacon ref) with
      owners:=Function.update (origins (PqxdhRecordLiftProtocol.markUsed before .beacon ref)).owners owner stored.origin} = _
    rw [mark_origins,resolved]
  · obtain rfl := eq_of_mem_support_pure _ supported
    rfl

/-- Administrative provenance is a computable update from the literal source query and returned success/handle, with no initial reachability or private-frame premise. -/
theorem capability (query : (CapabilitySpec n).Domain) (before : Control n)
    (result : (CapabilitySpec n).Range query × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.capability query before)) :
    origins result.2=PqxdhRecordLiftOrigins.annotate (.inr (.inl (.inr query))) result.1 (origins before) := by
  cases query with
  | installServer keyId identity ref => exact install_server keyId identity ref before result supported
  | installBeacon owner shell ref => exact install_beacon owner shell ref before result supported
  | peerPresent keyId | ownerPresent owner =>
    simp only [PqxdhRecordLiftProtocol.capability] at supported
    obtain rfl := eq_of_mem_support_pure _ supported
    rfl
  | appendOwner sender pin phase =>
    simp only [PqxdhRecordLiftProtocol.capability] at supported
    obtain rfl := eq_of_mem_support_pure _ supported
    exact origins_append (PqxdhRecordLiftProtocolHistory.view before) phase
  | hash bytes =>
    change result ∈ support ((fun reply => (reply,before)) <$> ((ServiceSpec n).query (.hash bytes) : OracleComp (ServiceSpec n) _)) at supported
    rw [support_map] at supported
    obtain ⟨reply,_called,rfl⟩ := supported
    rfl
  | advanceOwner owner phase =>
    simp only [PqxdhRecordLiftProtocol.capability] at supported
    split at supported
    · rename_i old present
      split at supported
      · obtain rfl := eq_of_mem_support_pure _ supported
        exact origins_owner_same (PqxdhRecordLiftProtocolHistory.view before) owner (.inactive old) (.inactive phase) present rfl
      · obtain rfl := eq_of_mem_support_pure _ supported
        rfl
    · obtain rfl := eq_of_mem_support_pure _ supported
      rfl

/-- Charged environment effects preserve the exact reply-driven origin update; public coins and hashes never masquerade as installations. -/
theorem effects (query : (EnvEffects n).Domain) (before : Control n)
    (result : (EnvEffects n).Range query × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.effects query before)) :
    origins result.2=PqxdhRecordLiftOrigins.annotate (.inr (.inl query)) result.1 (origins before) := by
  change result ∈ support ((PqxdhRecordLiftProtocol.effects query).run before) at supported
  unfold PqxdhRecordLiftProtocol.effects at supported
  rw [StateT.run_bind,StateT.run_lift,bind_pure_comp,mem_support_bind_iff] at supported
  obtain ⟨charged,chargedCalled,continued⟩ := supported
  rw [support_map] at chargedCalled
  obtain ⟨chargedReply,_charged,rfl⟩ := chargedCalled
  cases query with
  | inl coin =>
    simp only [StateT.run_lift,bind_pure_comp,support_map] at continued
    obtain ⟨reply,_called,same⟩ := continued
    subst result
    rfl
  | inr query => exact capability query before result continued

private theorem import_origins (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : Control n)
    (result : Unit × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.initializeServer created before)) :
    origins result.2=origins before := by
  cases present : before.server with
  | some server =>
    simp only [PqxdhRecordLiftProtocol.initializeServer,present] at supported
    obtain rfl := eq_of_mem_support_pure _ supported
    rfl
  | none =>
    simp only [PqxdhRecordLiftProtocol.initializeServer,present] at supported
    obtain rfl := eq_of_mem_support_pure _ supported
    apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
    · funext keyId
      cases entry : created.server.server.peers keyId <;>
        simp [PqxdhRecordLiftProtocolHistory.view,PqxdhRecordLiftProtocol.join,present,
          Server.fromKnown,PqxdhRecordLiftWorld.importedServer,Peer.fromKnown,entry,StoredKernel.origin]
    · rfl

/-- Every supported reply of the actual free record controller reconstructs its final opaque slot map solely from its query/reply annotation. -/
theorem query (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (request : (WorldSpec n).Domain) (before : Control n)
    (result : (WorldSpec n).Range request × Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.handler decode route request before)) :
    origins result.2=PqxdhRecordLiftOrigins.annotate request result.1 (origins before) := by
  cases request with
  | inl created => exact import_origins created before result supported
  | inr request => cases request with
    | inl effect => exact effects effect before result supported
    | inr record => cases record with
      | inl request => cases request with
        | inl send => exact server_step decode route (.inl send) before result supported
        | inr raw => exact server_step decode route (.inr raw) before result supported
      | inr request =>
        obtain ⟨owner,request⟩ := request
        cases request with
        | inl plaintext => exact beacon_step decode owner (.inl plaintext) before result supported
        | inr raw => exact beacon_step decode owner (.inr raw) before result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.server_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.server_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.beacon_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.beacon_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.capability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl.query
