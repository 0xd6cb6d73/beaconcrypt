import BeaconcryptCore.Computational.RawCtxGenericRoleStorage
import BeaconcryptCore.Computational.RawCtxGenericOwnerMap

/-!
The original Server routing, identity-derived associated-data lookup and same-peer selection are parameterized by the private kernel representation. Raw header routing precedes the exact owner validation; sending retains AD lookup and sender selection before empty-input rejection. Complete peer maps, metadata, optional replies and every raw attempt remain present. The source correspondence is operational and does not assume distinct peer identities, target-free family state or freshness.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericServer
open RawCtxGenericRoleStorage

noncomputable def peerAssociatedData {Kernel Metadata PeerMetadata : Type}
    (server : Server Kernel Metadata PeerMetadata) (kid : Std.U64) : Option Pqxdh.Bytes := do
  let peer ← server.peers kid
  pure (RawCtxServerRouting.associatedBytes server.identity peer.identity)

def selectedOwner {Kernel PeerMetadata : Type} (kid : Std.U64) (ad : Pqxdh.Bytes)
    (peer : Peer Kernel PeerMetadata) (attempts : Nat) : RawCtxChainOwner.State Kernel PeerMetadata :=
  ⟨peer.kernel, kid, ad, peer.metadata, attempts⟩

def putPeer {Kernel Metadata PeerMetadata : Type} (server : Server Kernel Metadata PeerMetadata)
    (kid : Std.U64) (peer : Peer Kernel PeerMetadata) (kernel : Kernel) : Server Kernel Metadata PeerMetadata :=
  {server with peers := Function.update server.peers kid (some {peer with kernel := kernel})}

noncomputable def rawServer {Kernel Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : ServerState Kernel Metadata PeerMetadata) :
    m (core.option.Option RawCtxWholeOwner.Decrypted × ServerState Kernel Metadata PeerMetadata) :=
  match route raw with
  | none => pure (.None, {state with rawAttempts := state.rawAttempts + 1})
  | some kid =>
      match peerAssociatedData state.server kid with
      | none => pure (.None, {state with rawAttempts := state.rawAttempts + 1})
      | some ad =>
          match state.server.peers kid with
          | none => pure (.None, {state with rawAttempts := state.rawAttempts + 1})
          | some peer => do
              let result ← (RawCtxChainOwner.rawReceive calls decode raw).run (selectedOwner kid ad peer state.rawAttempts)
              pure (result.1, ⟨putPeer state.server kid peer result.2.kernel, result.2.rawAttempts⟩)

noncomputable def sendServer {Kernel Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : ServerState Kernel Metadata PeerMetadata) :
    m (Option RawCtxSourceSend.Encrypted × ServerState Kernel Metadata PeerMetadata) :=
  match peerAssociatedData state.server kid with
  | none => pure (none, state)
  | some ad =>
      let sender := senderId state.server.metadata
      match state.server.peers kid with
      | none => pure (none, state)
      | some peer => do
          let result ← (RawCtxChainOwner.sendOwner calls sender plaintext).run (selectedOwner kid ad peer state.rawAttempts)
          pure (result.1, ⟨putPeer state.server kid peer result.2.kernel, result.2.rawAttempts⟩)

noncomputable def serverImpl {Kernel Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxServerMixed.SourceSpec (StateT (ServerState Kernel Metadata PeerMetadata) m) :=
  fun query state => match query with
  | .inl (plaintext, kid) => sendServer calls senderId plaintext kid state
  | .inr raw => rawServer calls route decode raw state

/-- The same original identities supply associated data after any private kernel interpretation. -/
theorem associated_map {Kernel Other Metadata PeerMetadata : Type} (interpret : Kernel → Other)
    (state : ServerState Kernel Metadata PeerMetadata) (kid : Std.U64) :
    peerAssociatedData (mapServer interpret state).server kid = peerAssociatedData state.server kid := by
  cases found : state.server.peers kid <;> simp [peerAssociatedData, mapServer, found, mapPeer]

/-- Publication changes the same assigned peer and retains every other complete entry, including equal-identity aliases. -/
theorem put_map {Kernel Other Metadata PeerMetadata : Type} (interpret : Kernel → Other)
    (state : ServerState Kernel Metadata PeerMetadata) (kid : Std.U64) (peer : Peer Kernel PeerMetadata)
    (kernel : Kernel) (attempts : Nat) :
    mapServer interpret (⟨putPeer state.server kid peer kernel, attempts⟩ : ServerState Kernel Metadata PeerMetadata) =
      ⟨putPeer (mapServer interpret state).server kid (mapPeer interpret peer) (interpret kernel), attempts⟩ := by
  simp only [mapServer, putPeer]
  congr 1
  congr 1
  funext other
  by_cases same : other = kid
  · subst other
    simp only [Function.update_self, Option.map_some]
    rfl
  · simp only [Function.update_of_ne same]

/-- Exact route, AD lookup, peer selection and raw publication commute with the private kernel map. -/
theorem raw_map {Kernel Other Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m) (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : ServerState Kernel Metadata PeerMetadata) :
    rawServer otherCalls route decode raw (mapServer interpret state) =
      Prod.map id (mapServer interpret) <$> rawServer calls route decode raw state := by
  simp only [rawServer, associated_map]
  cases routed : route raw with
  | some kid =>
    cases adFound : peerAssociatedData state.server kid with
    | some ad =>
      cases found : state.server.peers kid with
      | some peer =>
        simp only [adFound, mapServer, found, Option.map_some, bind_pure_comp]
        have mapped := RawCtxGenericOwnerMap.raw_map interpret calls otherCalls receiveMap decode raw
          (selectedOwner kid ad peer state.rawAttempts)
        change (RawCtxChainOwner.rawReceive otherCalls decode raw).run
          (selectedOwner kid ad (mapPeer interpret peer) state.rawAttempts) = _ at mapped
        rw [mapped, Functor.map_map, Functor.map_map]
        congr 1
        funext result
        simp only [Prod.map_apply, id_eq]
        exact congrArg (Prod.mk result.1) (put_map interpret state kid peer result.2.kernel result.2.rawAttempts).symm
      | none => simp [adFound, mapServer, found, Prod.map_apply]
    | none => simp [adFound, mapServer, Prod.map_apply]
  | none => simp [mapServer, Prod.map_apply]

/-- Source sends retain AD and sender lookup order and publish the same advanced peer on every optional outcome. -/
theorem send_map {Kernel Other Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m) (otherCalls : RawCtxChainOwner.Calls Other m)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : ServerState Kernel Metadata PeerMetadata) :
    sendServer otherCalls senderId plaintext kid (mapServer interpret state) =
      Prod.map id (mapServer interpret) <$> sendServer calls senderId plaintext kid state := by
  simp only [sendServer, associated_map]
  cases adFound : peerAssociatedData state.server kid with
  | some ad =>
    cases found : state.server.peers kid with
    | some peer =>
      simp only [mapServer, found, Option.map_some, bind_pure_comp]
      have mapped := RawCtxGenericOwnerMap.send_map interpret calls otherCalls sendMap
        (senderId state.server.metadata) plaintext (selectedOwner kid ad peer state.rawAttempts)
      change (RawCtxChainOwner.sendOwner otherCalls (senderId state.server.metadata) plaintext).run
        (selectedOwner kid ad (mapPeer interpret peer) state.rawAttempts) = _ at mapped
      rw [mapped, Functor.map_map, Functor.map_map]
      congr 1
      funext result
      simp only [Prod.map_apply, id_eq]
      exact congrArg (Prod.mk result.1) (put_map interpret state kid peer result.2.kernel result.2.rawAttempts).symm
    | none => simp [mapServer, found, Prod.map_apply]
  | none => simp [Prod.map_apply]

/-- Every original Server API query retains its complete optional reply and interpreted peer family. -/
theorem server_map {Kernel Other Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m) (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : ServerState Kernel Metadata PeerMetadata) :
    (serverImpl otherCalls senderId route decode query).run (mapServer interpret state) =
      Prod.map id (mapServer interpret) <$> (serverImpl calls senderId route decode query).run state := by
  cases query with
  | inl request => exact send_map interpret calls otherCalls sendMap senderId request.1 request.2 state
  | inr raw => exact raw_map interpret calls otherCalls receiveMap route decode raw state

/-- Any adaptive mixed Server schedule preserves all original API replies, every peer and all effects. -/
theorem schedule_map {Kernel Other Metadata PeerMetadata Result : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m) (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerMixed.SourceSpec Result) (state : ServerState Kernel Metadata PeerMetadata) :
    (simulateQ (serverImpl otherCalls senderId route decode) client).run (mapServer interpret state) =
      Prod.map id (mapServer interpret) <$> (simulateQ (serverImpl calls senderId route decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq (serverImpl calls senderId route decode)
    (serverImpl otherCalls senderId route decode) (mapServer interpret)
    (fun query state => (server_map interpret calls otherCalls receiveMap sendMap senderId route decode query state).symm)
    client state).symm

end BeaconcryptCore.Computational.RawCtxGenericServer

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServer.associated_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServer.associated_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServer.put_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServer.put_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServer.raw_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServer.raw_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServer.send_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServer.send_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServer.server_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServer.server_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServer.schedule_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServer.schedule_map
