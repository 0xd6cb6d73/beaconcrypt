import BeaconcryptCore.Computational.RawCtxGenericRoleFamily
import BeaconcryptCore.Computational.RawCtxGenericServer
import BeaconcryptCore.Computational.RawCtxGenericBeacon

/-!
The full finite family dispatches each original Server or Beacon request to the exact indexed generic role frontend and updates only that returned role state. Public services use the same supplied handler outside both role families. The same chain-independent original client can interleave arbitrary requests and stop adaptively while all installed peers, inactive phases and backend effects remain private and intact.

The two complete representation laws consume exact receive/send call-map equations; they do not assume target freshness, parent-table consistency or kernel independence. Concrete native and retained-slot interpreters must discharge those call equations in the source composition. This module supplies no key distribution or cryptographic advantage. Original raw parsing, admission and publication remain in the checked role frontends; snapshots and persistence are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily

noncomputable def impl {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolRoles.SourceSpec serverCount beaconCount)
      (StateT (Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) m) :=
  fun query state => match query with
  | .inl ⟨index, request⟩ => do
      let result ← (RawCtxGenericServer.serverImpl calls senderId route decode request).run (state.1 index)
      pure (result.1, (Function.update state.1 index result.2, state.2))
  | .inr (.inl ⟨index, request⟩) => do
      let result ← (RawCtxGenericBeacon.impl calls decode request).run (state.2 index)
      pure (result.1, (state.1, Function.update state.2 index result.2))
  | .inr (.inr request) => do
      let reply ← publicCalls request
      pure (reply, state)

set_option backward.isDefEq.respectTransparency false in
/-- Every selected role update commutes with the whole-family kernel map and keeps all other roles unchanged. -/
theorem step_map {Kernel Other Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Domain)
    (state : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (impl otherCalls publicCalls senderId route decode query).run (mapRoles interpret state) =
      Prod.map id (mapRoles interpret) <$> (impl calls publicCalls senderId route decode query).run state := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  all_goals simp only [impl, StateT.run, mapRoles, bind_pure_comp]
  case inl =>
    have mapped := congrArg (fun computation => (fun result =>
      (result.1, (Function.update (fun index => mapServer interpret (state.1 index)) index result.2,
        fun index => mapBeacon interpret (state.2 index)))) <$> computation)
      (RawCtxGenericServer.server_map interpret calls otherCalls receiveMap sendMap senderId route decode request (state.1 index))
    convert mapped using 1
    · rfl
    · simp only [Functor.map_map]
      congr 1
      funext result
      simp only [Prod.map_def, id_eq, mapRoles]
      congr 1
      exact congrArg (fun updated => (updated, fun index => mapBeacon interpret (state.2 index)))
        (Function.comp_update (mapServer interpret) state.1 index result.2)
  case inr.inl =>
    have mapped := congrArg (fun computation => (fun result =>
      (result.1, (fun index => mapServer interpret (state.1 index),
        Function.update (fun index => mapBeacon interpret (state.2 index)) index result.2))) <$> computation)
      (RawCtxGenericBeacon.step_map interpret calls otherCalls receiveMap sendMap decode request (state.2 index))
    convert mapped using 1 <;> try rfl
    simp only [Functor.map_map]
    congr 1
    funext result
    simp only [Prod.map_def, id_eq, mapRoles]
    congr 1
    exact congrArg (fun updated => (fun index => mapServer interpret (state.1 index), updated))
      (Function.comp_update (mapBeacon interpret) state.2 index result.2)
  case inr.inr => simp [Functor.map_map, Prod.map_def, mapRoles]

/-- The original adaptive family client receives identical replies while every role and backend effect is retained. -/
theorem schedule_map {Kernel Other Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec serverCount beaconCount) Result)
    (state : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (simulateQ (impl otherCalls publicCalls senderId route decode) client).run (mapRoles interpret state) =
      Prod.map id (mapRoles interpret) <$> (simulateQ (impl calls publicCalls senderId route decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq (impl calls publicCalls senderId route decode)
    (impl otherCalls publicCalls senderId route decode) (mapRoles interpret)
    (fun query state => (step_map interpret calls otherCalls publicCalls receiveMap sendMap senderId route decode query state).symm)
    client state).symm

end BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend.step_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend.step_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend.schedule_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend.schedule_map
