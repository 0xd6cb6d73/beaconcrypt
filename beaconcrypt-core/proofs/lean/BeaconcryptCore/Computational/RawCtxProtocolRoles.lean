import BeaconcryptCore.Computational.RawCtxRoleFamily

/-!
Both indexed Server and Beacon families interleave through one concrete fixed-source backend and one shared CTX cache. Public randomness, commitment requests and real HKDF projections remain outside either family and work even when either family is empty. Two complete-state equations identify the actual selected source operations through arbitrary adaptive cross-role scheduling and stopping. Native replies and primitive effects, including rejection and rollback effects, are retained.

The source role instances and their private fields are supplied at entry and may share identities, roots or record keys. These equations introduce no independence, freshness, challenge-selection or computational security premise. Typed instance handles identify existing API objects; hostile wire identifiers are still parsed and checked by the source. Allocation/generation, registration transitions, public network observation versus privileged API plaintext, explicit live reveals and all adjacent cryptographic hybrid simulations remain separate work. Snapshots, persistence, restoration and their consequences are excluded from the active protocol proof.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxProtocolRoles
open RawCtxRoleFamily

abbrev SourceSpec (serverCount beaconCount : Nat) :=
  FamilySpec RawCtxServerMixed.SourceSpec serverCount +
    (FamilySpec RawCtxMixedOwner.SourceSpec beaconCount + RawCtxServerServices.PublicSpec)

abbrev State (Metadata PeerMetadata Identity DhPair KemPair : Type)
    (serverCount beaconCount : Nat) :=
  (Fin serverCount → RawCtxServerRouting.State Metadata PeerMetadata) ×
    (Fin beaconCount → RawCtxBeaconLifecycle.State Identity DhPair KemPair)

/-- Both protocol roles and public services use one backend, retaining all installed role states. -/
noncomputable def protocolImpl {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
        (OracleComp RawCtxServerServices.BackendSpec)) :=
  fun query state => match query with
  | .inl request => do
      let result ← simulateQ RawCtxServerServices.nativeLift
        ((familyImpl serverCount (RawCtxServerMixed.serverImpl senderId route decode) request).run state.1)
      pure (result.1, (result.2, state.2))
  | .inr (.inl request) => do
      let result ← simulateQ RawCtxServerServices.nativeLift
        ((familyImpl beaconCount (RawCtxBeaconLifecycle.beaconImpl decode) request).run state.2)
      pure (result.1, (state.1, result.2))
  | .inr (.inr request) => do
      let result ← RawCtxServerServices.publicLift request
      pure (result, state)

/-- Actual selected source operations retain the same global primitive state across both roles and public services. -/
noncomputable def sourceImpl {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
        RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request => do
      let result ← (sourceFamily serverCount (RawCtxServerMixed.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
        senderId route decode) request).run (state.1.1, state.2)
      pure (result.1, ((result.2.1, state.1.2), result.2.2))
  | .inr (.inl request) => do
      let result ← (sourceFamily beaconCount (RawCtxBeaconLifecycle.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
        decode) request).run (state.1.2, state.2)
      pure (result.1, ((state.1.1, result.2.1), result.2.2))
  | .inr (.inr request) => do
      let result ← (((RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift)
        request).run state.2)
      pure (result.1, (state.1, result.2))

/-- Full source interpretation retains both replicated role families and the single shared primitive state. -/
theorem protocol_interpretation {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    ((RawCtxProtocolBackend.backend source writer).mapStateTBase
      (protocolImpl (PeerMetadata := PeerMetadata) (Identity := Identity) (DhPair := DhPair) (KemPair := KemPair)
        serverCount beaconCount senderId route decode)).flattenStateT =
      (sourceImpl (Auxiliary := Auxiliary) source writer serverCount beaconCount senderId route decode) := by
  funext query state
  rcases query with server | (beacon | publicQuery)
  all_goals simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, protocolImpl, sourceImpl,
    StateT.run, StateT.mk, bind_pure_comp, simulateQ_map]
  case inl =>
    rw [RawCtxProtocolBackend.backend, ← QueryImpl.simulateQ_compose,
      RawCtxServerServices.native_interpretation, ← RawCtxRoleFamily.server_interpretation]
    simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk]
    change (fun x => (x.1.1, x.1.2, x.2)) <$>
      (((fun a => (a.1, a.2, state.1.2)) <$>
        simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
          (familyImpl serverCount (RawCtxServerMixed.serverImpl senderId route decode) server state.1.1)).run state.2) = _
    rw [StateT.run_map]
    simp only [Functor.map_map, StateT.run]
    rfl
  case inr.inl =>
    rw [RawCtxProtocolBackend.backend, ← QueryImpl.simulateQ_compose,
      RawCtxServerServices.native_interpretation, ← RawCtxRoleFamily.beacon_interpretation]
    simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk]
    change (fun x => (x.1.1, x.1.2, x.2)) <$>
      (((fun a => (a.1, state.1.1, a.2)) <$>
        simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
          (familyImpl beaconCount (RawCtxBeaconLifecycle.beaconImpl decode) beacon state.1.2)).run state.2) = _
    rw [StateT.run_map]
    simp only [Functor.map_map, StateT.run]
    rfl
  case inr.inr =>
    change (fun x => (x.1.1, x.1.2, x.2)) <$>
      (((fun a => (a, state.1)) <$>
        simulateQ (RawCtxProtocolBackend.backend source writer)
          (RawCtxServerServices.publicLift publicQuery)).run state.2) = _
    rw [StateT.run_map]
    simp only [Functor.map_map, QueryImpl.compose, StateT.run]
    rfl

/-- Arbitrary adaptive cross-role delivery, requests, public queries and stopping preserve the whole protocol/primitive execution. -/
theorem schedule_interpretation {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RawCtxProtocolBackend.backend source writer)
      ((simulateQ (protocolImpl serverCount beaconCount senderId route decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl source writer serverCount beaconCount senderId route decode) client).run
          (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, protocol_interpretation]

end BeaconcryptCore.Computational.RawCtxProtocolRoles

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolRoles.protocol_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolRoles.protocol_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolRoles.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolRoles.schedule_interpretation
