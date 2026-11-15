-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.MldsaServerRouting

/-!
Pointwise public-AD routing preserves the supplied complete AD151 at every peer. This helper only projects bookkeeping metadata after the current populated-AD router has emitted its actual requests; it never recovers identities from an opaque digest or specializes the historical identity-prefix router. Actual Native routing selects its installed per-peer metadata independently.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet.concrete
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.MldsaPublicAdServerRouting

open RawCtxServerRouting
variable {Metadata : Type}

abbrev AssociatedData := Std.Array Std.U8 151#usize

def forgetPeer (peer : Peer AssociatedData) : Peer Unit := ⟨peer.identity, peer.kernel, ()⟩

def forgetServer (server : Server Metadata AssociatedData) : Server Metadata Unit :=
  ⟨server.identity, fun keyId => (server.peers keyId).map forgetPeer, server.metadata⟩

def forgetState (state : State Metadata AssociatedData) : State Metadata Unit :=
  ⟨forgetServer state.server, state.rawAttempts⟩

def liftPeer (associatedData : AssociatedData) (peer : Peer Unit) : Peer AssociatedData :=
  ⟨peer.identity, peer.kernel, associatedData⟩

def liftServer (associatedData : AssociatedData) (server : Server Metadata Unit) : Server Metadata AssociatedData :=
  ⟨server.identity, fun keyId => (server.peers keyId).map (liftPeer associatedData), server.metadata⟩

def liftState (associatedData : AssociatedData) (state : State Metadata Unit) : State Metadata AssociatedData :=
  ⟨liftServer associatedData state.server, state.rawAttempts⟩

/-- The pointwise model retains the same supplied complete AD at every installed peer. -/
def PublicAD (associatedData : AssociatedData) (server : Server Metadata AssociatedData) : Prop :=
  ∀ keyId peer, server.peers keyId = some peer → peer.metadata = associatedData

/-- Lifting the metadata-free map attaches the supplied complete AD to each existing peer. -/
theorem public_liftServer (associatedData : AssociatedData) (server : Server Metadata Unit) : PublicAD associatedData (liftServer associatedData server) := by
  intro keyId peer found
  obtain ⟨original, _present, same⟩ := Option.map_eq_some_iff.mp found
  exact same ▸ Eq.refl _

/-- Forgetting a lift recovers the original peer map without changing identities or ratchets. -/
theorem forget_liftServer (associatedData : AssociatedData) (server : Server Metadata Unit) : forgetServer (liftServer associatedData server) = server := by
  cases server with
  | mk identity peers metadata =>
    simp only [forgetServer, liftServer]
    congr 1
    funext keyId
    cases peers keyId <;> simp [forgetPeer, liftPeer]

/-- The projected state round-trip also retains the raw-attempt counter exactly. -/
theorem forget_liftState (associatedData : AssociatedData) (state : State Metadata Unit) :
    forgetState (liftState associatedData state) = state := by
  cases state
  simp only [forgetState, liftState, forget_liftServer]

/-- The pointwise invariant justifies restoring exactly the metadata that was projected away. -/
theorem lift_forgetServer (associatedData : AssociatedData) (server : Server Metadata AssociatedData)
    (publicAD : PublicAD associatedData server) :
    liftServer associatedData (forgetServer server) = server := by
  cases server with
  | mk identity peers metadata =>
    simp only [forgetServer, liftServer]
    congr 1
    funext keyId
    cases found : peers keyId with
    | none => simp
    | some peer =>
      have exactAD := publicAD keyId peer found
      cases peer
      simp only [forgetPeer, liftPeer, Option.map_some] at *
      simp [exactAD]

/-- No state coordinate is lost when projecting a map satisfying the pointwise invariant. -/
theorem lift_forgetState (associatedData : AssociatedData) (state : State Metadata AssociatedData)
    (publicAD : PublicAD associatedData state.server) :
    liftState associatedData (forgetState state) = state := by
  cases state
  simp only [forgetState, liftState, lift_forgetServer associatedData _ publicAD]

/-- Updating a selected ratchet preserves the supplied AD and every other complete peer. -/
theorem public_putPeer (associatedData : AssociatedData) (server : Server Metadata AssociatedData) (keyId : Std.U64)
    (peer : Peer AssociatedData) (kernel : ConcreteRatchetKernel)
    (found : server.peers keyId = some peer) (publicAD : PublicAD associatedData server) :
    PublicAD associatedData (putPeer server keyId peer kernel) := by
  intro other next foundNext
  by_cases same : other = keyId
  · subst other
    simp only [putPeer, Function.update_self, Option.some.injEq] at foundNext
    exact foundNext ▸ publicAD keyId peer found
  · simp only [putPeer, Function.update_of_ne same] at foundNext
    exact publicAD other next foundNext

/-- Installing a peer with the supplied AD preserves the pointwise invariant. -/
theorem public_insert (associatedData : AssociatedData) (server : Server Metadata AssociatedData) (keyId : Std.U64) (identity : Identity)
    (kernel : ConcreteRatchetKernel) (publicAD : PublicAD associatedData server) :
    PublicAD associatedData { server with peers := (Function.update server.peers keyId
      (some ⟨identity, kernel, associatedData⟩)) } := by
  intro other peer found
  by_cases same : other = keyId
  · subst other
    simp only [Function.update_self, Option.some.injEq] at found
    exact found ▸ Eq.refl _
  · simp only [Function.update_of_ne same] at found
    exact publicAD other peer found

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

/-- The pointwise public-AD handler projects only metadata after executing the current router on the same supplied AD. -/
noncomputable def handlerPublic (associatedData : AssociatedData)
    (sender : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxServerMixed.SourceSpec
      (StateT (State Metadata Unit) (OracleComp RawCtxMixedOwner.NativeSpec)) :=
  fun query state => (fun result => (result.1, forgetState result.2)) <$>
    (MldsaServerRouting.handler PqxdhRefinement.absBytes sender route decode query).run
      (liftState associatedData state)

/-- Under the installed-AD invariant, projection preserves every current primitive query, reply and poststate. -/
theorem handler_public (associatedData : AssociatedData)
    (sender : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State Metadata AssociatedData)
    (publicAD : PublicAD associatedData state.server) :
    (fun result => (result.1, forgetState result.2)) <$>
        (MldsaServerRouting.handler PqxdhRefinement.absBytes sender route decode query).run state =
      (handlerPublic associatedData sender route decode query).run (forgetState state) := by
  simp only [handlerPublic, StateT.run, lift_forgetState associatedData state publicAD]

/-- Every actual send outcome preserves immutable supplied AD, including a failed seal or writer. -/
theorem send_preserves_public (associatedData : AssociatedData) (sender : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (keyId : Std.U64)
    (state : State Metadata AssociatedData) (publicAD : PublicAD associatedData state.server)
    (result : Option RawCtxSourceSend.Encrypted × State Metadata AssociatedData)
    (supported : result ∈ support (MldsaServerRouting.send PqxdhRefinement.absBytes sender plaintext keyId state)) :
    PublicAD associatedData result.2.server := by
  cases found : state.server.peers keyId
  case none =>
    simp only [MldsaServerRouting.send, found, support_pure, Set.mem_singleton_iff] at supported
    exact supported.symm ▸ publicAD
  case some peer =>
    simp only [MldsaServerRouting.send, found, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨sent, _possible, rfl⟩ := supported
    exact public_putPeer associatedData state.server keyId peer sent.2.owner.kernel found publicAD

/-- Every actual raw outcome preserves immutable supplied AD, including malformed frames and failed opening. -/
theorem receive_preserves_public (associatedData : AssociatedData) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata AssociatedData) (publicAD : PublicAD associatedData state.server)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × State Metadata AssociatedData)
    (supported : result ∈ support (MldsaServerRouting.receive PqxdhRefinement.absBytes route decode raw state)) :
    PublicAD associatedData result.2.server := by
  cases routed : route raw
  case none =>
    simp only [MldsaServerRouting.receive, routed, support_pure, Set.mem_singleton_iff] at supported
    exact supported.symm ▸ publicAD
  case some keyId =>
    cases found : state.server.peers keyId
    case none =>
      simp only [MldsaServerRouting.receive, routed, found, support_pure, Set.mem_singleton_iff] at supported
      exact supported.symm ▸ publicAD
    case some peer =>
      simp only [MldsaServerRouting.receive, routed, found, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨opened, _possible, rfl⟩ := supported
      exact public_putPeer associatedData state.server keyId peer opened.2.owner.kernel found publicAD

/-- The actual populated-AD router preserves its pointwise supplied-AD invariant. -/
theorem handler_preserves_public (associatedData : AssociatedData) (sender : Metadata → Std.U64) (route : SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State Metadata AssociatedData) (publicAD : PublicAD associatedData state.server)
    (result : RawCtxServerMixed.SourceSpec.Range query × State Metadata AssociatedData)
    (supported : result ∈ support ((MldsaServerRouting.handler PqxdhRefinement.absBytes sender route decode query).run state)) :
    PublicAD associatedData result.2.server :=
  match query with
  | .inl (plaintext, keyId) => send_preserves_public associatedData sender plaintext keyId state publicAD result supported
  | .inr raw => receive_preserves_public associatedData route decode raw state publicAD result supported

/-- The source send handle or the decoded raw route chooses the same peer in the pointwise model. -/
def routedTarget (route : SenderDecoder) : RawCtxServerMixed.SourceSpec.Domain → Option Std.U64
  | .inl (_, keyId) => some keyId
  | .inr raw => route raw

/-- The actual record-owner program under a Server query strips only its separately routed handle. -/
noncomputable def recordOwner (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (keyId : Std.U64) (associatedData : AssociatedData)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) (rawAttempts : Nat) :
    (query : RawCtxServerMixed.SourceSpec.Domain) →
      OracleComp RawCtxMixedOwner.NativeSpec (RawCtxServerMixed.SourceSpec.Range query × RawCtxWholeOwner.OwnerState Unit)
  | .inl (plaintext, _) => (RawCtxMixedOwner.ownerImpl sender decode (.inl plaintext)).run
      ⟨⟨kernel, keyId, PqxdhRefinement.absBytes associatedData, ()⟩, rawAttempts⟩
  | .inr raw => (RawCtxMixedOwner.ownerImpl sender decode (.inr raw)).run
      ⟨⟨kernel, keyId, PqxdhRefinement.absBytes associatedData, ()⟩, rawAttempts⟩

/-- The pointwise current handler on a selected peer runs the actual record owner with the supplied complete AD, then retains the original Unit bookkeeping. -/
theorem handler_peer (associatedData : AssociatedData) (sender : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State Metadata Unit)
    (keyId : Std.U64) (peer : Peer Unit)
    (target : (routedTarget route query) = some keyId)
    (found : state.server.peers keyId = some peer) :
    (handlerPublic associatedData sender route decode query).run state =
      (fun result => (result.1, (⟨putPeer state.server keyId peer result.2.owner.kernel,
        result.2.rawAttempts⟩ : State Metadata Unit))) <$>
        recordOwner (sender state.server.metadata) decode keyId associatedData peer.kernel state.rawAttempts query := by
  have restored := forget_liftServer associatedData state.server
  dsimp only [liftServer] at restored
  have peer_unit : (⟨peer.identity, peer.kernel, ()⟩ : Peer Unit) = peer := by
    cases peer with
    | mk identity kernel metadata => cases metadata; rfl
  rcases query with ⟨plaintext, sent⟩ | raw
  · simp only [routedTarget, Option.some.injEq] at target
    subst sent
    simp [handlerPublic, StateT.run, MldsaServerRouting.handler, MldsaServerRouting.send,
      liftState, liftServer, liftPeer, found, MldsaServerRouting.selected,
      recordOwner, RawCtxMixedOwner.ownerImpl, Functor.map_map, bind_pure_comp, forgetState, forget_putPeer,
      restored, forgetPeer, peer_unit]
  · change route raw = some keyId at target
    simp [handlerPublic, StateT.run, MldsaServerRouting.handler, MldsaServerRouting.receive,
      target, liftState, liftServer, liftPeer, found, MldsaServerRouting.selected,
      recordOwner, RawCtxMixedOwner.ownerImpl, Functor.map_map, bind_pure_comp, forgetState, forget_putPeer,
      restored, forgetPeer, peer_unit]

/-- Missing selected peers reject before any record primitive, retaining the exact raw-attempt increment. -/
theorem handler_absent (associatedData : AssociatedData) (sender : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State Metadata Unit)
    (absent : ∀ keyId, (routedTarget route query) = some keyId →
      state.server.peers keyId = none) :
    (handlerPublic associatedData sender route decode query).run state =
      pure (match query with
        | .inl _ => (none, state)
        | .inr _ => (.None, { state with rawAttempts := state.rawAttempts + 1 })) := by
  have restored := forget_liftServer associatedData state.server
  dsimp only [liftServer] at restored
  rcases query with ⟨plaintext, keyId⟩ | raw
  · have missing := absent keyId rfl
    simp [handlerPublic, StateT.run, MldsaServerRouting.handler, MldsaServerRouting.send,
      liftState, liftServer, missing, forgetState, restored]
  · cases target : route raw with
    | none =>
      simp [handlerPublic, StateT.run, MldsaServerRouting.handler, MldsaServerRouting.receive,
        target, liftState, forgetState, forget_liftServer]
    | some keyId =>
      have missing := absent keyId target
      simp [handlerPublic, StateT.run, MldsaServerRouting.handler, MldsaServerRouting.receive,
        target, liftState, liftServer, missing, forgetState, restored]

/-- Every outcome preserves the original Server identity while executing the current AD-bearing router. -/
theorem handler_identity (associatedData : AssociatedData) (sender : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State Metadata Unit)
    (result : RawCtxServerMixed.SourceSpec.Range query × State Metadata Unit)
    (supported : result ∈ support ((handlerPublic associatedData sender route decode query).run state)) :
    result.2.server.identity = state.server.identity := by
  cases target : (routedTarget route query) with
  | none =>
    rw [handler_absent associatedData sender route decode query state
      (fun keyId found => by simp only [target, reduceCtorEq] at found)] at supported
    rw [support_pure, Set.mem_singleton_iff] at supported
    subst result
    cases query <;> rfl
  | some keyId =>
    cases found : state.server.peers keyId with
    | none =>
      rw [handler_absent associatedData sender route decode query state
        (fun other routed => by simp only [target, Option.some.injEq] at routed; subst other; exact found)] at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst result
      cases query <;> rfl
    | some peer =>
      rw [handler_peer associatedData sender route decode query state keyId peer target found,
        support_map] at supported
      obtain ⟨inner, _called, same⟩ := supported
      exact (congrArg (fun value => value.2.server.identity) same).symm

/-- Current supplied-AD routing retains the existing per-direction primitive caps. -/
theorem handler_bound (associatedData : AssociatedData) (sender : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State Metadata Unit)
    (kind : RawCtxMixedOwner.CallKind) :
    ((handlerPublic associatedData sender route decode query).run state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind)
      (match query with | .inl _ => RawCtxMixedOwner.sendCost kind | .inr _ => RawCtxMixedOwner.receiveCost kind) := by
  simp only [handlerPublic, StateT.run, isQueryBoundP_map_iff]
  rcases query with ⟨plaintext, keyId⟩ | raw
  · exact MldsaServerRouting.send_bound _ sender plaintext keyId _ kind
  · exact MldsaServerRouting.raw_bound _ route decode raw _ kind

end BeaconcryptCore.Computational.MldsaPublicAdServerRouting

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.public_liftServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.public_liftServer

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_liftServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_liftServer

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_liftState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_liftState

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.lift_forgetServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.lift_forgetServer

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.lift_forgetState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.lift_forgetState

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.public_putPeer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.public_putPeer

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.public_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.public_insert

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_putPeer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_putPeer

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.forget_insert

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_public

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.send_preserves_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.send_preserves_public

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.receive_preserves_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.receive_preserves_public

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_preserves_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_preserves_public

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_peer

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_absent

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_identity

/-- info: 'BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaPublicAdServerRouting.handler_bound
