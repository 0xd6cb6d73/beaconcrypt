import BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend
import BeaconcryptCore.Computational.RawCtxGenericFamilyRead

/-!
The actual finite-role request schedule is extended by original current-chain and skipped-material reads. Each read privately receives the kernel selected from the complete family at the original owner, returns its original dependent optional reply, and appends that request/reply at the exact original history position. All other operations tick the same history. Kernel-map laws preserve the complete family and history under exact receive, send and read effect equations, and retain the same public services and original adaptive client.

These statements do not provide a hidden-input observer with unknown native bytes or a target-dependent freshness decision. A masked Slot reader must discharge the appropriate event coupling; byte aliases and public guesses remain explicit candidate events. The read payload and final whole state are private interpreter data. Native source interpretation, resource accounting and security advantages are separate consuming results. Snapshot and persistence behavior are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericFamilyLive
open RawCtxGenericRoleFamily RawCtxGenericFamilyRead RawCtxProtocolReveals

abbrev State (Kernel Metadata PeerMetadata Identity DhPair KemPair : Type) (serverCount beaconCount : Nat) :=
  RawCtxGenericRoleFamily.Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
    History serverCount beaconCount

def mapState {Kernel Other Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → Other)
    (state : State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    State Other Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount :=
  (mapRoles interpret state.1, state.2)

def nativeState {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → ConcreteRatchetKernel)
    (state : State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount :=
  (nativeRoles interpret state.1, state.2)

noncomputable def impl {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (reader : QueryImpl (ReadSpec Kernel serverCount beaconCount) m)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec serverCount beaconCount)
      (StateT (State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) m) :=
  fun query state => match query with
  | .inl request => do
      let result ← (RawCtxGenericFamilyFrontend.impl calls publicCalls senderId route decode request).run state.1
      pure (result.1, (result.2, tick state.2))
  | .inr request => do
      let reply ← reader (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) state.1)
      pure (reply, (state.1, note ⟨request, reply⟩ state.2))

/-- Original live reads forward the actual selected kernel and record the original optional reply at the original API position. -/
theorem read_step {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (reader : QueryImpl (ReadSpec Kernel serverCount beaconCount) m)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : Request serverCount beaconCount)
    (state : State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (impl calls publicCalls reader senderId route decode (.inr request)).run state = (do
      let reply ← reader (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) state.1)
      pure (reply, (state.1, note ⟨request, reply⟩ state.2))) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete original role/read step commutes with kernel conversion and retains the exact actual read history. -/
theorem step_map {Kernel Other Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (reader : QueryImpl (ReadSpec Kernel serverCount beaconCount) m)
    (otherReader : QueryImpl (ReadSpec Other serverCount beaconCount) m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (readMap : ∀ request kernel, otherReader (request, kernel.map interpret) = reader (request, kernel))
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).Domain)
    (state : State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (impl otherCalls publicCalls otherReader senderId route decode query).run (mapState interpret state) =
      Prod.map id (mapState interpret) <$> (impl calls publicCalls reader senderId route decode query).run state := by
  cases query with
  | inl request =>
      have mapped := congrArg (fun computation => (fun result => (result.1, (result.2, tick state.2))) <$> computation)
        (RawCtxGenericFamilyFrontend.step_map interpret calls otherCalls publicCalls receiveMap sendMap
          senderId route decode request state.1)
      simpa only [impl, StateT.run, mapState, bind_pure_comp, Functor.map_map, Prod.map_def, Function.comp_def, id_eq] using mapped
  | inr request =>
      simp only [impl, StateT.run, mapState, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
      have selected := congrArg (fun kernel : Option Other => (show m ((RevealSpec serverCount beaconCount).Range request) from otherReader (request, kernel)))
        (RawCtxGenericRoleFamily.map_selected interpret (requestOwner request) state.1)
      exact congrArg (fun computation => (fun reply =>
        (reply, (mapRoles interpret state.1, note ⟨request, reply⟩ state.2))) <$> computation)
        (selected.trans (readMap request _))

/-- Every adaptive original record/public/live-read continuation retains all role state, optional replies and exact history. -/
theorem schedule_map {Kernel Other Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (reader : QueryImpl (ReadSpec Kernel serverCount beaconCount) m)
    (otherReader : QueryImpl (ReadSpec Other serverCount beaconCount) m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (readMap : ∀ request kernel, otherReader (request, kernel.map interpret) = reader (request, kernel))
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (simulateQ (impl otherCalls publicCalls otherReader senderId route decode) client).run (mapState interpret state) =
      Prod.map id (mapState interpret) <$> (simulateQ (impl calls publicCalls reader senderId route decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq (impl calls publicCalls reader senderId route decode)
    (impl otherCalls publicCalls otherReader senderId route decode) (mapState interpret)
    (fun query state => (step_map interpret calls otherCalls publicCalls reader otherReader receiveMap sendMap readMap
      senderId route decode query state).symm) client state).symm

end BeaconcryptCore.Computational.RawCtxGenericFamilyLive

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyLive.read_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyLive.read_step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyLive.step_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyLive.step_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyLive.schedule_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyLive.schedule_map

