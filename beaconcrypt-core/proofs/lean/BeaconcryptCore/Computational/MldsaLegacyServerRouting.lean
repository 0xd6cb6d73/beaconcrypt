-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.MldsaServerRouting

/-!
The old deployment environment installs identity-derived associated data. Its specialization of the populated-AD router must retain that operational invariant before forgetting peer metadata. These source equalities preserve every primitive request and optional reply; they assert no equality for arbitrary populated AD.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.MldsaLegacyServerRouting

open RawCtxServerRouting
variable {Metadata : Type}

abbrev AssociatedData := Std.Array Std.U8 281#usize

def forgetPeer (peer : Peer AssociatedData) : Peer Unit := ⟨peer.identity, peer.kernel, ()⟩

def forgetServer (server : Server Metadata AssociatedData) : Server Metadata Unit :=
  ⟨server.identity, fun keyId => (server.peers keyId).map forgetPeer, server.metadata⟩

def forgetState (state : State Metadata AssociatedData) : State Metadata Unit :=
  ⟨forgetServer state.server, state.rawAttempts⟩

noncomputable def liftPeer (identity : Identity) (peer : Peer Unit) : Peer AssociatedData :=
  ⟨peer.identity, peer.kernel, associatedArray identity peer.identity⟩

noncomputable def liftServer (server : Server Metadata Unit) : Server Metadata AssociatedData :=
  ⟨server.identity, fun keyId => (server.peers keyId).map (liftPeer server.identity), server.metadata⟩

/-- An internal legacy invariant on the actual immutable per-peer associated data. -/
def LegacyAD (server : Server Metadata AssociatedData) : Prop :=
  ∀ keyId peer, server.peers keyId = some peer → peer.metadata = associatedArray server.identity peer.identity

/-- Importing a legacy native peer map derives its complete identity-based AD invariant. -/
theorem legacy_liftServer (server : Server Metadata Unit) : LegacyAD (liftServer server) := by
  intro keyId peer found
  obtain ⟨original, _present, same⟩ := Option.map_eq_some_iff.mp found
  exact same ▸ Eq.refl _

/-- Erasing a legacy import recovers exactly the original native peer map. -/
theorem forget_liftServer (server : Server Metadata Unit) : forgetServer (liftServer server) = server := by
  cases server with
  | mk identity peers metadata =>
    simp only [forgetServer, liftServer]
    congr 1
    funext keyId
    cases peers keyId <;> simp [forgetPeer, liftPeer]

/-- Updating a selected ratchet leaves its legacy AD and every other installed peer intact. -/
theorem legacy_putPeer (server : Server Metadata AssociatedData) (keyId : Std.U64)
    (peer : Peer AssociatedData) (kernel : ConcreteRatchetKernel)
    (found : server.peers keyId = some peer) (legacy : LegacyAD server) :
    LegacyAD (putPeer server keyId peer kernel) := by
  intro other next foundNext
  by_cases same : other = keyId
  · subst other
    simp only [putPeer, Function.update_self, Option.some.injEq] at foundNext
    exact foundNext ▸ legacy keyId peer found
  · simp only [putPeer, Function.update_of_ne same] at foundNext
    exact legacy other next foundNext

/-- A legacy installation derives the invariant for its newly attached complete AD. -/
theorem legacy_insert (server : Server Metadata AssociatedData) (keyId : Std.U64) (identity : Identity)
    (kernel : ConcreteRatchetKernel) (legacy : LegacyAD server) :
    LegacyAD { server with peers := (Function.update server.peers keyId
      (some ⟨identity, kernel, associatedArray server.identity identity⟩)) } := by
  intro other peer found
  by_cases same : other = keyId
  · subst other
    simp only [Function.update_self, Option.some.injEq] at found
    exact found ▸ Eq.refl _
  · simp only [Function.update_of_ne same] at found
    exact legacy other peer found

theorem forget_putPeer (server : Server Metadata AssociatedData) (keyId : Std.U64)
    (peer : Peer AssociatedData) (kernel : ConcreteRatchetKernel) :
    forgetServer (putPeer server keyId peer kernel) =
      putPeer (forgetServer server) keyId (forgetPeer peer) kernel :=
  congrArg (fun peers : Std.U64 → Option (Peer Unit) => Server.mk server.identity peers server.metadata)
    (funext fun other => by
      by_cases same : other = keyId <;>
        simp [putPeer, forgetServer, forgetPeer, Function.update_apply, same])

/-- Forgetting an installed peer preserves its exact identity and ratchet at the same handle. -/
theorem forget_insert (server : Server Metadata AssociatedData) (keyId : Std.U64)
    (peer : Peer AssociatedData) :
    forgetServer { server with peers := Function.update server.peers keyId (some peer) } =
      { forgetServer server with peers := Function.update (forgetServer server).peers keyId (some (forgetPeer peer)) } :=
  forget_putPeer server keyId peer peer.kernel

/-- The source send in a legacy world has the exact old deployment law after metadata erasure. -/
theorem send_legacy (sender : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (keyId : Std.U64)
    (state : State Metadata AssociatedData) (legacy : LegacyAD state.server) :
    (fun result => (result.1, forgetState result.2)) <$>
        MldsaServerRouting.send PqxdhRefinement.absBytes sender plaintext keyId state =
      RawCtxServerMixed.sendServer sender plaintext keyId (forgetState state) := by
  cases found : state.server.peers keyId
  case none =>
    simp [MldsaServerRouting.send, RawCtxServerMixed.sendServer, RawCtxServerSend.sendServer,
      peerAssociatedData, forgetState, forgetServer, found]
  case some peer =>
    simp [MldsaServerRouting.send, RawCtxServerMixed.sendServer, RawCtxServerSend.sendServer,
      peerAssociatedData, forgetState, forgetServer, found, forgetPeer, legacy keyId _ found,
      MldsaServerRouting.selected, selectedOwner, RawCtxMixedOwner.ownerImpl,
      bind_pure_comp, Functor.map_map, associatedBytes, RawCtxMixedOwner.sendAdapter,
      ← QueryImpl.simulateQ_compose, putPeer, Function.update_apply, apply_ite]
    congr 1
    funext result
    congr 3
    exact funext fun other => (Function.update_apply
      (fun keyId => (state.server.peers keyId).map forgetPeer) keyId
      (some ⟨peer.identity, result.2.owner.kernel, ()⟩) other).symm

/-- The same specialization preserves raw routing, rejection and every opening request. -/
theorem receive_legacy (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata AssociatedData) (legacy : LegacyAD state.server) :
    (fun result => (result.1, forgetState result.2)) <$>
        MldsaServerRouting.receive PqxdhRefinement.absBytes route decode raw state =
      RawCtxServerMixed.rawServer route decode raw (forgetState state) := by
  cases routed : route raw
  case none =>
    simp [MldsaServerRouting.receive, RawCtxServerMixed.rawServer, routed, forgetState]
  case some keyId =>
    cases found : state.server.peers keyId
    case none =>
      simp [MldsaServerRouting.receive, RawCtxServerMixed.rawServer, routed, peerAssociatedData,
        forgetState, forgetServer, found]
    case some peer =>
      simp [MldsaServerRouting.receive, RawCtxServerMixed.rawServer, routed, peerAssociatedData,
        forgetState, forgetServer, found, forgetPeer, legacy keyId _ found,
        MldsaServerRouting.selected, selectedOwner, RawCtxMixedOwner.ownerImpl,
        bind_pure_comp, Functor.map_map, associatedBytes, putPeer, Function.update_apply, apply_ite]
      congr 1
      funext result
      congr 3
      exact funext fun other => (Function.update_apply
        (fun keyId => (state.server.peers keyId).map forgetPeer) keyId
        (some ⟨peer.identity, result.2.owner.kernel, ()⟩) other).symm

/-- Both record directions specialize only after the actual immutable AD invariant is supplied. -/
theorem handler_legacy (sender : Metadata → Std.U64) (route : SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State Metadata AssociatedData) (legacy : LegacyAD state.server) :
    (fun result => (result.1, forgetState result.2)) <$>
        (MldsaServerRouting.handler PqxdhRefinement.absBytes sender route decode query).run state =
      (RawCtxServerMixed.serverImpl sender route decode query).run (forgetState state) :=
  match query with
  | .inl (plaintext, keyId) => send_legacy sender plaintext keyId state legacy
  | .inr raw => receive_legacy route decode raw state legacy

/-- Every actual send outcome preserves immutable legacy AD, including a failed seal or writer. -/
theorem send_preserves_legacy (sender : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (keyId : Std.U64)
    (state : State Metadata AssociatedData) (legacy : LegacyAD state.server)
    (result : Option RawCtxSourceSend.Encrypted × State Metadata AssociatedData)
    (supported : result ∈ support (MldsaServerRouting.send PqxdhRefinement.absBytes sender plaintext keyId state)) :
    LegacyAD result.2.server := by
  cases found : state.server.peers keyId
  case none =>
    simp only [MldsaServerRouting.send, found, support_pure, Set.mem_singleton_iff] at supported
    exact supported.symm ▸ legacy
  case some peer =>
    simp only [MldsaServerRouting.send, found, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨sent, _possible, rfl⟩ := supported
    exact legacy_putPeer state.server keyId peer sent.2.owner.kernel found legacy

/-- Every actual raw outcome preserves immutable legacy AD, including malformed frames and failed opening. -/
theorem receive_preserves_legacy (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata AssociatedData) (legacy : LegacyAD state.server)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × State Metadata AssociatedData)
    (supported : result ∈ support (MldsaServerRouting.receive PqxdhRefinement.absBytes route decode raw state)) :
    LegacyAD result.2.server := by
  cases routed : route raw
  case none =>
    simp only [MldsaServerRouting.receive, routed, support_pure, Set.mem_singleton_iff] at supported
    exact supported.symm ▸ legacy
  case some keyId =>
    cases found : state.server.peers keyId
    case none =>
      simp only [MldsaServerRouting.receive, routed, found, support_pure, Set.mem_singleton_iff] at supported
      exact supported.symm ▸ legacy
    case some peer =>
      simp only [MldsaServerRouting.receive, routed, found, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨opened, _possible, rfl⟩ := supported
      exact legacy_putPeer state.server keyId peer opened.2.owner.kernel found legacy

/-- The actual populated-AD router preserves its derived legacy specialization invariant. -/
theorem handler_preserves_legacy (sender : Metadata → Std.U64) (route : SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State Metadata AssociatedData) (legacy : LegacyAD state.server)
    (result : RawCtxServerMixed.SourceSpec.Range query × State Metadata AssociatedData)
    (supported : result ∈ support ((MldsaServerRouting.handler PqxdhRefinement.absBytes sender route decode query).run state)) :
    LegacyAD result.2.server :=
  match query with
  | .inl (plaintext, keyId) => send_preserves_legacy sender plaintext keyId state legacy result supported
  | .inr raw => receive_preserves_legacy route decode raw state legacy result supported

end BeaconcryptCore.Computational.MldsaLegacyServerRouting

/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.forget_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.forget_insert

/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.legacy_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.legacy_insert

/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.legacy_liftServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.legacy_liftServer
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.forget_liftServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.forget_liftServer
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.legacy_putPeer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.legacy_putPeer
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.forget_putPeer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.forget_putPeer
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.send_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.send_legacy
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.receive_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.receive_legacy
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.handler_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.handler_legacy
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.send_preserves_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.send_preserves_legacy
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.receive_preserves_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.receive_preserves_legacy
/-- info: 'BeaconcryptCore.Computational.MldsaLegacyServerRouting.handler_preserves_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaLegacyServerRouting.handler_preserves_legacy
