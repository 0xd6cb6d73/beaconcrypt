-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxServerMixed

/-!
Assigned-peer routing with authenticated session metadata. Each selected peer supplies its populated associated data to the existing mixed source owner. The entire peer map and primitive poststate survive optional errors. Concrete map storage and the native outer scheduler remain separate adapter boundaries.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet.concrete

set_option autoImplicit false

namespace BeaconcryptCore.Computational.MldsaServerRouting

open RawCtxServerRouting

variable {Metadata PeerMetadata Primitive Result : Type}
variable {ι : Type} {base : OracleSpec ι}

/-- Authentication metadata remains attached to the same assigned peer as its ratchet. -/
abbrev ServerState (Metadata PeerMetadata : Type) := RawCtxServerRouting.State Metadata PeerMetadata

def selected (associatedData : PeerMetadata → Pqxdh.Bytes) (kid : Std.U64)
    (peer : Peer PeerMetadata) : RawCtxWholeOwner.Owner Unit :=
  ⟨peer.kernel, kid, associatedData peer.metadata, ()⟩

/-- A send uses the Server sender ID and the selected authenticated peer's AD. -/
noncomputable def send (associatedData : PeerMetadata → Pqxdh.Bytes)
    (sender : Metadata → Std.U64) (plaintext : Pqxdh.Bytes)
    (kid : Std.U64) (state : ServerState Metadata PeerMetadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (Option RawCtxSourceSend.Encrypted × ServerState Metadata PeerMetadata) :=
  match state.server.peers kid with
  | none => pure (none, state)
  | some peer => do
      let result ← RawCtxMixedOwner.ownerImpl (sender state.server.metadata) (fun _ => none)
        (.inl plaintext) ⟨selected associatedData kid peer, state.rawAttempts⟩
      pure (result.1, ⟨putPeer state.server kid peer result.2.owner.kernel, result.2.rawAttempts⟩)

/-- Every raw delivery increments the attempt count, including failed routing. -/
noncomputable def receive (associatedData : PeerMetadata → Pqxdh.Bytes)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : ServerState Metadata PeerMetadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (core.option.Option RawCtxWholeOwner.Decrypted × ServerState Metadata PeerMetadata) :=
  match route raw with
  | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
  | some kid => match state.server.peers kid with
    | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
    | some peer => do
        let result ← RawCtxMixedOwner.ownerImpl (0#u64) decode (.inr raw)
          ⟨selected associatedData kid peer, state.rawAttempts⟩
        pure (result.1, ⟨putPeer state.server kid peer result.2.owner.kernel, result.2.rawAttempts⟩)

noncomputable def handler (associatedData : PeerMetadata → Pqxdh.Bytes)
    (sender : Metadata → Std.U64) (route : SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxServerMixed.SourceSpec
      (StateT (ServerState Metadata PeerMetadata) (OracleComp RawCtxMixedOwner.NativeSpec)) :=
  fun query state => match query with
  | .inl (plaintext, kid) => send associatedData sender plaintext kid state
  | .inr raw => receive associatedData route decode raw state

/-- One primitive state is shared by every assigned peer and every operation. -/
noncomputable def sourceStep
    (associatedData : PeerMetadata → Pqxdh.Bytes)
    (primitives : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp base)))
    (sender : Metadata → Std.U64) (route : SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxServerMixed.SourceSpec
      (StateT (ServerState Metadata PeerMetadata × Primitive) (OracleComp base)) :=
  (primitives.mapStateTBase (handler associatedData sender route decode)).flattenStateT

noncomputable def registrationStep
    (primitives : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp base)))
    (sender : Metadata → Std.U64) (route : SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxServerMixed.SourceSpec
      (StateT (ServerState Metadata session.CompletedRegistrationBinding × Primitive) (OracleComp base)) :=
  sourceStep (fun binding => PqxdhRefinement.absBytes binding.associated_data)
    primitives sender route decode

theorem selected_associated_data (associatedData : PeerMetadata → Pqxdh.Bytes)
    (kid : Std.U64) (peer : Peer PeerMetadata) :
    (selected associatedData kid peer).associatedData = associatedData peer.metadata := by
  rfl

theorem send_bound (associatedData : PeerMetadata → Pqxdh.Bytes)
    (sender : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : ServerState Metadata PeerMetadata) (kind : RawCtxMixedOwner.CallKind) :
    (send associatedData sender plaintext kid state).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = kind) (RawCtxMixedOwner.sendCost kind) := by
  cases found : state.server.peers kid with
  | none => simp [send, found]
  | some peer =>
      simp only [send, found, bind_pure_comp, isQueryBoundP_map_iff]
      exact RawCtxMixedOwner.send_bounds (sender state.server.metadata) (fun _ => none)
        plaintext _ kind

theorem raw_bound (associatedData : PeerMetadata → Pqxdh.Bytes)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : ServerState Metadata PeerMetadata) (kind : RawCtxMixedOwner.CallKind) :
    (receive associatedData route decode raw state).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = kind) (RawCtxMixedOwner.receiveCost kind) := by
  cases routed : route raw with
  | none => simp [receive, routed]
  | some kid =>
      cases found : state.server.peers kid with
      | none => simp [receive, routed, found]
      | some peer =>
          simp only [receive, routed, found, bind_pure_comp, isQueryBoundP_map_iff]
          exact RawCtxMixedOwner.receive_bounds (0#u64) decode raw _ kind

/-- Arbitrary peer selection retains the complete peer map and actual primitive poststate. -/
theorem schedule_interpretation (associatedData : PeerMetadata → Pqxdh.Bytes)
    (primitives : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp base)))
    (sender : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerMixed.SourceSpec Result)
    (state : ServerState Metadata PeerMetadata) (primitive : Primitive) :
    (simulateQ primitives ((simulateQ (handler associatedData sender route decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceStep associatedData primitives sender route decode) client).run (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  rfl

end BeaconcryptCore.Computational.MldsaServerRouting

/-- info: 'BeaconcryptCore.Computational.MldsaServerRouting.selected_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaServerRouting.selected_associated_data

/-- info: 'BeaconcryptCore.Computational.MldsaServerRouting.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaServerRouting.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.MldsaServerRouting.send_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaServerRouting.send_bound

/-- info: 'BeaconcryptCore.Computational.MldsaServerRouting.raw_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaServerRouting.raw_bound
