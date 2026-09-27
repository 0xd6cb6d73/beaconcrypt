import BeaconcryptCore.Computational.RawCtxPositionedOwner
import BeaconcryptCore.Computational.RawCtxProtocolRoles

/-!
Eight statements lift actual owner material positions through the existing Server map, all five Beacon phases, replicated role families and public services. Every enrolled Server peer and established Beacon retains its own supplied directional origins under the original full source computation. Actual optional failures, failed-send advancement, receive rollback and the complete common primitive state remain in the execution. Inactive phases and missing peers introduce no invented kernel.

The family theorem updates only the selected existing instance; the final step and adaptive schedule preserve all Server/Beacon positions jointly. Origins may be byte-equal across distinct handles or directions, and provided states may be correlated. No independent key table, key injectivity, decryption correctness, fresh-output sampling or factor for a cryptographic identity choice is inferred.

These are invariants of the fixed functional source and the original supplied role states. The adjacent owner initializer proves a concrete way to establish each kernel's starting relation; allocation, registration and the actual joint distribution of all supplied states are separate. Record compromise reads, snapshots/restores, evolving-key hybrid interpretation and network declassification must later consume the exact current-chain/cache position facts. The proof adds no public API, ghost history or primitive query. Native library, representation, runtime, persistence and global security obligations remain explicit.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxProtocolPositions
open RawCtxPositionedOwner RawCtxServerRouting

abbrev Origins := RatchetChain × RatchetChain

def ServerPositioned {Metadata PeerMetadata : Type} (c : Pqxdh.Crypto)
    (origins : Std.U64 → Origins) (server : Server Metadata PeerMetadata) : Prop :=
  ∀ kid peer, server.peers kid = some peer → Positioned c (origins kid).1 (origins kid).2 peer.kernel

/-- Publication preserves every unselected peer's original positions, even when key bytes coincide. -/
theorem putPeer_positions {Metadata PeerMetadata : Type} (c : Pqxdh.Crypto)
    (origins : Std.U64 → Origins) (server : Server Metadata PeerMetadata)
    (invariant : ServerPositioned c origins server) (kid : Std.U64)
    (peer : Peer PeerMetadata) (kernel : ConcreteRatchetKernel)
    (positioned : Positioned c (origins kid).1 (origins kid).2 kernel) :
    ServerPositioned c origins (putPeer server kid peer kernel) := by
  intro other selected present
  by_cases same : other = kid
  · simp only [same, putPeer_selected, Option.some.injEq] at present
    simpa only [same, ← present] using positioned
  · exact invariant other selected ((putPeer_other server kid other peer kernel same).symm.trans present)

/-- Actual server raw routing preserves every peer's source positions and the full primitive state. -/
theorem server_raw_positions {Metadata PeerMetadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (origins : Std.U64 → Origins) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : State Metadata PeerMetadata)
    (invariant : ServerPositioned source.crypto origins state.server)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support (RawCtxServerRouting.rawGame (receiveNative source)
      route decode raw state primitive)) :
    ServerPositioned source.crypto origins result.1.2.server := by
  rcases rawGame_cases (receiveNative source) route decode raw state primitive result present with
    rfl | ⟨kid, peer, opened, _, lookup, supported, rfl⟩
  · exact invariant
  · apply putPeer_positions source.crypto origins state.server invariant kid peer opened.1.2.owner.kernel
    exact raw_positions source (origins kid).1 (origins kid).2 decode raw _
      (invariant kid peer lookup) primitive opened supported

/-- Actual same-entry sends preserve positions on success, failure, empty input and exhaustion. -/
theorem server_send_positions {Metadata PeerMetadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (origins : Std.U64 → Origins) (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Metadata PeerMetadata)
    (invariant : ServerPositioned source.crypto origins state.server)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support (RawCtxServerSend.sendGame
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
        RawCtxMixedOwner.sendLift) senderId plaintext kid state primitive)) :
    ServerPositioned source.crypto origins result.1.2.server := by
  rcases RawCtxServerSend.sendGame_cases _ senderId plaintext kid state primitive result present with
    ⟨_, rfl⟩ | ⟨peer, sent, lookup, supported, rfl⟩
  · exact invariant
  · apply putPeer_positions source.crypto origins state.server invariant kid peer sent.1.2.owner.kernel
    apply sendOwner_positions source writer (origins kid).1 (origins kid).2
      (senderId state.server.metadata) plaintext
      ⟨selectedOwner kid (associatedBytes state.server.identity peer.identity) peer, state.rawAttempts⟩
      (invariant kid peer lookup) primitive sent
    have handler : ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
        RawCtxMixedOwner.sendLift) ∘ₛ RawCtxSourceSeal.nativeAdapter) = sendNative (Auxiliary := Auxiliary) source writer := by
      funext query
      exact QueryImpl.simulateQ_compose _ _ _
    simpa only [handler] using supported

/-- Either original server operation preserves every enrolled peer's source-position invariant. -/
theorem server_step_positions {Metadata PeerMetadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (origins : Std.U64 → Origins) (senderId : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State Metadata PeerMetadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : ServerPositioned source.crypto origins state.1.server)
    (result : RawCtxServerMixed.SourceSpec.Range query ×
      (State Metadata PeerMetadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((RawCtxServerMixed.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      senderId route decode query).run state)) :
    ServerPositioned source.crypto origins result.2.1.server := by
  rcases query with ⟨plaintext, kid⟩ | raw
  · change result ∈ support ((do
      let sent ← RawCtxServerSend.sendGame
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
          RawCtxMixedOwner.sendLift) senderId plaintext kid state.1 state.2
      pure (sent.1.1, (sent.1.2, sent.2))) : ProbComp _) at present
    obtain ⟨sent, supported, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    simpa only [equal] using server_send_positions source writer origins senderId plaintext kid state.1 invariant state.2 sent supported
  · change result ∈ support ((do
      let received ← RawCtxServerRouting.rawGame
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
          RawCtxMixedOwner.receiveAdapter) route decode raw state.1 state.2
      pure (received.1.1, (received.1.2, received.2))) : ProbComp _) at present
    rw [shared_receiveNative] at present
    obtain ⟨received, supported, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    simpa only [equal] using server_raw_positions source origins route decode raw state.1 invariant state.2 received supported

def BeaconPositioned {Identity DhPair KemPair : Type} (c : Pqxdh.Crypto) (origins : Origins)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) : Prop :=
  match state.beacon.phase with
  | .established _ _ kernel => Positioned c origins.1 origins.2 kernel
  | _ => True

/-- Actual Beacon phase dispatch preserves its original directional positions through every optional reply. -/
theorem beacon_step_positions {Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (origins : Origins) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair × RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : BeaconPositioned source.crypto origins state.1)
    (result : RawCtxMixedOwner.SourceSpec.Range query ×
      (RawCtxBeaconLifecycle.State Identity DhPair KemPair × RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((RawCtxBeaconLifecycle.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      decode query).run state)) :
    BeaconPositioned source.crypto origins result.2.1 := by
  cases phase : state.1.beacon.phase
  all_goals simp only [RawCtxBeaconLifecycle.sourceImpl, StateT.run, phase] at present
  case established control ad kernel =>
    obtain ⟨owned, supported, returned⟩ := mem_support_bind_peel _ _ present
    have aligned : Positioned source.crypto origins.1 origins.2 kernel := by
      simpa only [BeaconPositioned, phase] using invariant
    have equal := eq_of_mem_support_pure _ returned
    simpa only [equal, BeaconPositioned, RawCtxBeaconLifecycle.reinstall] using
      RawCtxPositionedOwner.step_positions source writer origins.1 origins.2 state.1.beacon.identityKeyId decode query
        (RawCtxBeaconLifecycle.selected state.1 control ad kernel, state.2) aligned owned supported
  all_goals have equal := eq_of_mem_support_pure _ present
  all_goals cases query <;> simp only [equal, RawCtxBeaconLifecycle.rejected, BeaconPositioned, phase]

/-- Existing family routing preserves each instance's own invariant and the same primitive poststate. -/
theorem family_positions {ι LocalState PrimitiveState : Type} {spec : OracleSpec ι}
    (count : Nat) (impl : QueryImpl spec (StateT (LocalState × PrimitiveState) ProbComp))
    (invariant : Fin count → LocalState → Prop)
    (step : ∀ index query state result, invariant index state.1 →
      result ∈ support ((impl query).run state) → invariant index result.2.1)
    (query : (RawCtxRoleFamily.FamilySpec spec count).Domain)
    (state : (Fin count → LocalState) × PrimitiveState)
    (initial : ∀ index, invariant index (state.1 index))
    (result : spec.Range query.2 × ((Fin count → LocalState) × PrimitiveState))
    (present : result ∈ support ((RawCtxRoleFamily.sourceFamily count impl query).run state)) :
    ∀ index, invariant index (result.2.1 index) := by
  change result ∈ support ((do
    let child ← (impl query.2).run (state.1 query.1, state.2)
    pure (child.1, (Function.update state.1 query.1 child.2.1, child.2.2))) : ProbComp _) at present
  obtain ⟨child, supported, returned⟩ := mem_support_bind_peel _ _ present
  rw [eq_of_mem_support_pure _ returned]
  intro index
  by_cases same : index = query.1
  · simpa only [same, Function.update_self] using
      step query.1 query.2 (state.1 query.1, state.2) child (initial query.1) supported
  · simpa only [Function.update_of_ne same] using initial index

def RolesPositioned {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (c : Pqxdh.Crypto) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins)
    (roles : RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) : Prop :=
  (∀ index, ServerPositioned c (serverOrigins index) (roles.1 index).server) ∧
    ∀ index, BeaconPositioned c (beaconOrigins index) (roles.2 index)

/-- Every original cross-role or public operation preserves all actual source material origins. -/
theorem protocol_step_positions {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins) (senderId : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : RolesPositioned source.crypto serverOrigins beaconOrigins state.1)
    (result : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Range query ×
      (RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
        RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((RawCtxProtocolRoles.sourceImpl source writer serverCount beaconCount senderId
      route decode query).run state)) :
    RolesPositioned source.crypto serverOrigins beaconOrigins result.2.1 := by
  rcases query with serverQuery | (beaconQuery | publicQuery)
  all_goals simp only [RawCtxProtocolRoles.sourceImpl, StateT.run] at present
  all_goals obtain ⟨child, supported, returned⟩ := mem_support_bind_peel _ _ present
  all_goals rw [eq_of_mem_support_pure _ returned]
  case inr.inr => exact invariant
  all_goals constructor
  case inl.right => exact invariant.2
  case inr.inl.left => exact invariant.1
  case inl.left =>
    exact family_positions serverCount _
      (fun index server => ServerPositioned source.crypto (serverOrigins index) server.server)
      (fun index query state result initial present =>
        server_step_positions source writer (serverOrigins index) senderId route decode query state initial result present)
      serverQuery (state.1.1, state.2) invariant.1 child supported
  case inr.inl.right =>
    exact family_positions beaconCount _
      (fun index beacon => BeaconPositioned source.crypto (beaconOrigins index) beacon)
      (fun index query state result initial present =>
        beacon_step_positions source writer (beaconOrigins index) decode query state initial result present)
      beaconQuery (state.1.2, state.2) invariant.2 child supported

/-- Every supported adaptive run retains the same original positions for both role families. -/
theorem protocol_schedule_positions {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins) (senderId : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : RolesPositioned source.crypto serverOrigins beaconOrigins state.1)
    (result : Result × (RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((simulateQ (RawCtxProtocolRoles.sourceImpl source writer serverCount beaconCount
      senderId route decode) client).run state)) :
    RolesPositioned source.crypto serverOrigins beaconOrigins result.2.1 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value => simpa using present ▸ invariant
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
    obtain ⟨reply, supported, continued⟩ := present
    exact ih reply.1 reply.2
      (protocol_step_positions source writer serverCount beaconCount serverOrigins beaconOrigins senderId
        route decode query state invariant reply supported) result continued

end BeaconcryptCore.Computational.RawCtxProtocolPositions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.putPeer_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.putPeer_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.server_raw_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.server_raw_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.server_send_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.server_send_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.server_step_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.server_step_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.beacon_step_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.beacon_step_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.family_positions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.family_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.protocol_step_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.protocol_step_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolPositions.protocol_schedule_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolPositions.protocol_schedule_positions
