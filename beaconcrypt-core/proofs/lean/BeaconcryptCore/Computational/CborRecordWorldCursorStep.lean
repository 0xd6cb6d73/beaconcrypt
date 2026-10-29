-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldCursor

/-! Actual routed Server and Beacon record operations update only the public sending cursors dictated by their original requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRecordWorldCursorStep
open CborRecordWorldClient (advance)
open CborRecordWorldCursor
variable {Metadata PeerMetadata Primitive ι : Type} {base : OracleSpec ι}

private theorem map_state_apply {Input Output : Type} (f : Input → Output)
    (work : StateT Primitive (OracleComp base) Input) (state : Primitive) :
    (f <$> work) state = Prod.map f id <$> work state :=
  bind_pure_comp (Prod.map f id) (work state)

/-- The cursor of every actual peer, independent of its authenticated AD and private chain bytes. -/
def peers (server : RawCtxServerRouting.Server Metadata PeerMetadata) : Std.U64 → Option Nat :=
  fun keyId => (server.peers keyId).map fun peer => peer.kernel.refined.control.send_sequence.val

def nextPeers (query : RawCtxServerMixed.SourceSpec.Domain)
    (server : RawCtxServerRouting.Server Metadata PeerMetadata) : Std.U64 → Option Nat :=
  match query with
  | .inl (plaintext, keyId) => Function.update (peers server) keyId ((peers server keyId).map (advance plaintext))
  | .inr _ => peers server

/-- Actual routing preserves every other peer and advances the selected cursor even on writer failure. -/
theorem server_cursor
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp base)))
    (associatedData : PeerMetadata → Pqxdh.Bytes) (sender : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : RawCtxServerRouting.State Metadata PeerMetadata)
    (primitive : Primitive) (result : (RawCtxServerMixed.SourceSpec.Range query ×
      RawCtxServerRouting.State Metadata PeerMetadata) × Primitive)
    (supported : result ∈ support ((simulateQ native
      ((MldsaServerRouting.handler associatedData sender route decode query).run state)).run primitive)) :
    peers result.1.2.server = nextPeers query state.server := by
  cases query with
  | inl pair =>
    rcases pair with ⟨plaintext, keyId⟩
    cases found : state.server.peers keyId with
    | none =>
      simp only [MldsaServerRouting.handler, StateT.run, MldsaServerRouting.send, found,
        simulateQ_pure] at supported
      subst result
      funext other
      by_cases same : other = keyId
      · subst other
        simp [nextPeers, peers, found]
      · simp [nextPeers, Function.update_of_ne same]
    | some peer =>
      simp only [MldsaServerRouting.handler, StateT.run, MldsaServerRouting.send, found,
        bind_pure_comp, simulateQ_map, map_state_apply, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      have moved := mixed_cursor native (sender state.server.metadata) (fun _ => none) (.inl plaintext)
        ⟨MldsaServerRouting.selected associatedData keyId peer, state.rawAttempts⟩ primitive inner reached
      funext other
      by_cases same : other = keyId
      · subst other
        simpa only [Prod.map, id_eq, peers, nextPeers, RawCtxServerRouting.putPeer, Function.update_self,
          found, Option.map_some, MldsaServerRouting.selected] using congrArg some moved
      · simp only [Prod.map, id_eq, peers, nextPeers, RawCtxServerRouting.putPeer, Function.update_of_ne same]
  | inr raw =>
    cases routed : route raw with
    | none =>
      simp only [MldsaServerRouting.handler, StateT.run, MldsaServerRouting.receive, routed,
        simulateQ_pure] at supported
      subst result
      rfl
    | some keyId =>
      cases found : state.server.peers keyId with
      | none =>
        simp only [MldsaServerRouting.handler, StateT.run, MldsaServerRouting.receive, routed, found,
          simulateQ_pure] at supported
        subst result
        rfl
      | some peer =>
        simp only [MldsaServerRouting.handler, StateT.run, MldsaServerRouting.receive, routed, found,
          bind_pure_comp, simulateQ_map, map_state_apply, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        have kept := mixed_cursor native (0#u64) decode (.inr raw)
          ⟨MldsaServerRouting.selected associatedData keyId peer, state.rawAttempts⟩ primitive inner reached
        funext other
        by_cases same : other = keyId
        · subst other
          simpa only [Prod.map, id_eq, peers, nextPeers, RawCtxServerRouting.putPeer, Function.update_self,
            found, Option.map_some, MldsaServerRouting.selected] using congrArg some kept
        · simp only [Prod.map, id_eq, peers, nextPeers, RawCtxServerRouting.putPeer, Function.update_of_ne same]

/-- Inactive phases have no public send cursor. -/
def phaseCursor : PqxdhRecordLiftBeacon.Phase → Option CborRecordWorldClient.Cursor
  | .inactive _ => none
  | .established shell kernel => some ⟨shell.identityKeyId, kernel.refined.control.send_sequence.val⟩

def nextPhase (query : RawCtxMixedOwner.SourceSpec.Domain)
    (phase : PqxdhRecordLiftBeacon.Phase) : Option CborRecordWorldClient.Cursor :=
  match query with
  | .inl plaintext => (phaseCursor phase).map fun cursor => { cursor with sequence := advance plaintext cursor.sequence }
  | .inr _ => phaseCursor phase

/-- Actual Beacon rejection, send and receive branches retain exactly their public cursor transition. -/
theorem beacon_cursor
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhRecordLiftBeacon.State) (primitive : Primitive)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftBeacon.State) × Primitive)
    (supported : result ∈ support ((simulateQ native
      ((PqxdhRecordLiftBeacon.handler decode query).run state)).run primitive)) :
    phaseCursor result.1.2.phase = nextPhase query state.phase := by
  cases phase : state.phase with
  | inactive inactive =>
    cases query <;>
      simp only [PqxdhRecordLiftBeacon.handler, StateT.run, phase,
        PqxdhRecordLiftBeacon.rejected, simulateQ_pure] at supported <;>
      subst result <;> simp only [phaseCursor, nextPhase, phase, Option.map_none]
  | established shell kernel =>
    simp only [PqxdhRecordLiftBeacon.handler, StateT.run, phase, bind_pure_comp,
      simulateQ_map, map_state_apply, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have counter := mixed_cursor native shell.identityKeyId decode query
      ⟨⟨kernel, shell.control.server_binding.identity_key_id, PqxdhRefinement.absBytes shell.associatedData, ()⟩,
        state.rawAttempts⟩ primitive inner reached
    cases query <;> simp only [Prod.map, id_eq, phaseCursor, nextPhase, Option.map_some] <;> rw [counter]

def serverQuery {n : Nat} (query : RawCtxServerMixed.SourceSpec.Domain) : (PqxdhRecordLiftInterface.WorldSpec n).Domain :=
  .inr (.inr (.inl query))

/-- The instrumented World retains exactly the routed source cursor transition, including its literal writer log. -/
theorem world_server_cursor {n : Nat} {κ KemSK Reader Response : Type} {extra : OracleSpec κ}
    (setup : PqxdhServerAuthExperiment.Setup extra KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhRecordLiftWorld.State n)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.serverStep setup codec route query).run state)) :
    worldShell result.2 = CborRecordWorldClient.next (serverQuery (n := n) query)
      ((PqxdhRecordLiftInterface.server_reply query).symm ▸ result.1) (worldShell state) := by
  cases existing : state.server with
  | none =>
    cases query <;>
      simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, existing, mem_support_pure_iff] at supported <;>
      subst result <;> simp only [worldShell, serverQuery, CborRecordWorldClient.next,
        CborRecordWorldClient.advanceServer, existing, Option.map_none]
  | some server =>
    simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, existing, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have original := logged_support (PqxdhRecordLiftWorld.primitives setup codec)
      ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _ => server.sender)
        route codec.frameRead query).run server.records) state.primitive inner reached
    have moved := server_cursor (PqxdhRecordLiftWorld.primitives setup codec) PqxdhRefinement.absBytes
      (fun _ => server.sender) route codec.frameRead query server.records state.primitive
      (inner.1.1, inner.2) original
    cases query with
    | inl pair =>
      rcases pair with ⟨plaintext, keyId⟩
      unfold nextPeers peers at moved
      simp only [worldShell, serverQuery, CborRecordWorldClient.next, CborRecordWorldClient.advanceServer,
        PqxdhRecordLiftWorld.produce, existing, Option.map_some, ]
      exact congrArg (fun cursors => CborRecordWorldClient.Shell.mk (some ⟨server.sender, cursors⟩)
          (worldShell state).owners) moved
    | inr raw =>
      unfold nextPeers peers at moved
      simp only [worldShell, serverQuery, CborRecordWorldClient.next,
        PqxdhRecordLiftWorld.produce, existing, Option.map_some, ]
      exact congrArg (fun cursors => CborRecordWorldClient.Shell.mk (some ⟨server.sender, cursors⟩)
          (worldShell state).owners) moved

private theorem shell_ext (left right : CborRecordWorldClient.Shell)
    (server : left.server = right.server) (owners : left.owners = right.owners) : left = right := by
  cases left
  cases right
  cases server
  cases owners
  rfl

def beaconQuery {n : Nat} (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    (PqxdhRecordLiftInterface.WorldSpec n).Domain := .inr (.inr (.inr (owner, query)))

/-- Actual instrumented Beacon operations agree with the public cursor update even when no ciphertext is returned. -/
theorem world_beacon_cursor {n : Nat} {κ KemSK Reader Response : Type} {extra : OracleSpec κ}
    (setup : PqxdhServerAuthExperiment.Setup extra KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhRecordLiftWorld.State n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.beaconStep setup codec owner query).run state)) :
    worldShell result.2 = CborRecordWorldClient.next (beaconQuery (n := n) owner query)
      ((PqxdhRecordLiftInterface.beacon_reply owner query).symm ▸ result.1) (worldShell state) := by
  cases found : state.owners[owner]? with
  | none =>
    simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, found, mem_support_pure_iff] at supported
    subst result
    cases query with
    | inr raw => rfl
    | inl plaintext =>
      apply shell_ext
      · rfl
      · funext other
        by_cases same : other = owner
        · subst other
          simp only [worldShell, beaconQuery, CborRecordWorldClient.next, CborRecordWorldClient.advanceOwner,
            found, Option.bind_none, Function.update_self, Option.map_none]
        · simp only [worldShell, beaconQuery, CborRecordWorldClient.next, CborRecordWorldClient.advanceOwner,
            Function.update_of_ne same]
  | some phase =>
    simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, found, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have original := logged_support (PqxdhRecordLiftWorld.primitives setup codec)
      ((PqxdhRecordLiftBeacon.handler codec.frameRead query).run ⟨phase, state.ownerRaw owner⟩)
      state.primitive inner reached
    have moved := beacon_cursor (PqxdhRecordLiftWorld.primitives setup codec) codec.frameRead query
      ⟨phase, state.ownerRaw owner⟩ state.primitive (inner.1.1, inner.2) original
    have within := (List.getElem?_eq_some_iff.mp found).1
    cases query with
    | inl plaintext =>
      apply shell_ext
      · rfl
      · funext other
        by_cases same : other = owner
        · subst other
          simp only [worldShell, beaconQuery, CborRecordWorldClient.next, CborRecordWorldClient.advanceOwner,
            PqxdhRecordLiftWorld.produce, List.getElem?_set_self within, Function.update_self,
            found, Option.bind_some, ]
          exact moved
        · simp only [worldShell, beaconQuery, CborRecordWorldClient.next, CborRecordWorldClient.advanceOwner,
            PqxdhRecordLiftWorld.produce, List.getElem?_set_ne (Ne.symm same), Function.update_of_ne same]
    | inr raw =>
      apply shell_ext
      · rfl
      · funext other
        by_cases same : other = owner
        · subst other
          simp only [worldShell, beaconQuery, CborRecordWorldClient.next,
            PqxdhRecordLiftWorld.produce, List.getElem?_set_self within,
            found, Option.bind_some, ]
          exact moved
        · simp only [worldShell, beaconQuery, CborRecordWorldClient.next,
            PqxdhRecordLiftWorld.produce, List.getElem?_set_ne (Ne.symm same)]

end BeaconcryptCore.Computational.CborRecordWorldCursorStep

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorStep.server_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorStep.server_cursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorStep.beacon_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorStep.beacon_cursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorStep.world_server_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorStep.world_server_cursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorStep.world_beacon_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorStep.world_beacon_cursor
