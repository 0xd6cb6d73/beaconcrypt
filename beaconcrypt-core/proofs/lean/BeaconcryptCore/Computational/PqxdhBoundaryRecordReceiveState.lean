-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution

/-! Current owner/Beacon receive state and resource consumers use AD151/CTX227. current_server_interpretation/current_server_bounds consume the same installed-metadata Server source bridge. The retained server_bounds statement concerns only the explicitly historical CE identity-AD routing model. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState
open PqxdhRefinement PqxdhBoundaryRecordExecution
variable {Message Root Metadata PrimitiveState ι : Type} {base : OracleSpec ι}

/-- Interpreting the complete receive transcription preserves the full owner and primitive state under the original raw game. -/
theorem owner_interpretation (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 151#usize) (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (associated : state.owner.associatedData = absBytes ad)
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (primitive : PrimitiveState) :
    (simulateQ impl (executeOwner reader ad erased raw state)).run primitive =
      (fun result => (ok result.1, result.2)) <$>
        RawCtxWholeOwner.rawGame (impl ∘ₛ RawCtxMixedOwner.receiveAdapter)
          (RawCtxFrameDecoding.decode reader.model) raw state primitive := by
  rw [executeOwner_exact reader ad erased raw state associated,
    PqxdhBoundaryRecordPrelude.owner_exact reader ad raw state (0#u64) associated]
  simp only [RawCtxWholeOwner.rawGame, simulateQ_map, StateT.run_map, QueryImpl.simulateQ_compose]
  rfl

/-- Every completed interpreted receive has the same complete optional reply, owner and primitive state in the original raw game. -/
theorem owner_supported (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 151#usize) (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (associated : state.owner.associatedData = absBytes ad)
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (primitive finalPrimitive : PrimitiveState)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata)
    (supported : (ok result, finalPrimitive) ∈ support ((simulateQ impl (executeOwner reader ad erased raw state)).run primitive)) :
    (result, finalPrimitive) ∈ support (RawCtxWholeOwner.rawGame (impl ∘ₛ RawCtxMixedOwner.receiveAdapter)
      (RawCtxFrameDecoding.decode reader.model) raw state primitive) := by
  rw [owner_interpretation reader ad erased raw state associated impl primitive] at supported
  simp only [support_map, Set.mem_image, Prod.mk.injEq, RustM.ok.injEq] at supported
  obtain ⟨⟨actual, final⟩, stepped, rfl, rfl⟩ := supported
  exact stepped

/-- Failed live receive restores the entire owned protocol state; its actual primitive/cache poststate remains separate and is not rolled back. -/
theorem owner_failure (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 151#usize) (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state after : RawCtxWholeOwner.OwnerState Metadata) (associated : state.owner.associatedData = absBytes ad)
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (primitive finalPrimitive : PrimitiveState)
    (supported : (ok (.None, after), finalPrimitive) ∈ support
      ((simulateQ impl (executeOwner reader ad erased raw state)).run primitive)) :
    after.owner = state.owner ∧ after.rawAttempts = state.rawAttempts + 1 := by
  have actual := owner_supported reader ad erased raw state associated impl primitive finalPrimitive (.None, after) supported
  exact ⟨RawCtxWholeOwner.rawGame_failure_owner _ _ _ _ _ _ actual rfl,
    (RawCtxWholeOwner.rawGame_preserves_metadata _ _ _ _ _ _ actual).1⟩

/-- Every completed raw receive counts one attempt and retains the pinned sender, associated data and role metadata. -/
theorem owner_metadata (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 151#usize) (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (associated : state.owner.associatedData = absBytes ad)
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (primitive finalPrimitive : PrimitiveState)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata)
    (supported : (ok result, finalPrimitive) ∈ support
      ((simulateQ impl (executeOwner reader ad erased raw state)).run primitive)) :
    result.2.rawAttempts = state.rawAttempts + 1 ∧
      result.2.owner.expectedSender = state.owner.expectedSender ∧
      result.2.owner.associatedData = state.owner.associatedData ∧
      result.2.owner.metadata = state.owner.metadata :=
  RawCtxWholeOwner.rawGame_preserves_metadata _ _ _ _ _ _
    (owner_supported reader ad erased raw state associated impl primitive finalPrimitive result supported)

/-- The actual owner execution inherits the complete source receive callback caps, including rejected and failed attempts. -/
theorem owner_bounds (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 151#usize) (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (associated : state.owner.associatedData = absBytes ad)
    (kind : RawCtxMixedOwner.CallKind) :
    (executeOwner reader ad erased raw state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind) (RawCtxMixedOwner.receiveCost kind) := by
  rw [executeOwner_exact reader ad erased raw state associated,
    PqxdhBoundaryRecordPrelude.owner_exact reader ad raw state (0#u64) associated,
    isQueryBoundP_map_iff]
  exact RawCtxMixedOwner.receive_bounds _ _ _ _ _

/-- The retained historical CE routing model preserves the same raw-model callback caps; current_server_bounds is the current stored-AD source statement. -/
theorem server_bounds {PeerMetadata : Type} (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) (kind : RawCtxMixedOwner.CallKind) :
    (executeServer reader erased raw state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind) (RawCtxMixedOwner.receiveCost kind) := by
  rw [executeServer_exact, PqxdhBoundaryRecordPrelude.server_exact, isQueryBoundP_map_iff]
  exact RawCtxServerMixed.raw_bound _ _ _ _ _

/-- Interpreting current metadata-routed Server execution retains the complete result, selected peer map, raw counter and primitive/cache poststate of the same current handler. -/
theorem current_server_interpretation {PeerMetadata : Type}
    (sessionData : PeerMetadata → Std.Array Std.U8 151#usize)
    (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata)
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (primitive : PrimitiveState) :
    (simulateQ impl (currentExecuteServer sessionData reader erased raw state)).run primitive =
      (fun result => (ok result.1, result.2)) <$>
        (simulateQ impl (MldsaServerRouting.receive (fun metadata => absBytes (sessionData metadata))
          (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) raw state)).run primitive := by
  rw [currentExecuteServer_source, simulateQ_map, StateT.run_map]

/-- Every current selected-metadata receive retains the complete original all-attempt callback bill, including failed routing, decode, KDF and opening branches. -/
theorem current_server_bounds {PeerMetadata : Type}
    (sessionData : PeerMetadata → Std.Array Std.U8 151#usize)
    (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) (kind : RawCtxMixedOwner.CallKind) :
    (currentExecuteServer sessionData reader erased raw state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind) (RawCtxMixedOwner.receiveCost kind) := by
  rw [currentExecuteServer_source, isQueryBoundP_map_iff]
  exact MldsaServerRouting.raw_bound _ _ _ _ _ _

/-- Every Beacon lifecycle branch preserves the complete receive callback caps. -/
theorem beacon_bounds {Identity DhPair KemPair : Type} (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) (kind : RawCtxMixedOwner.CallKind) :
    (executeBeacon reader erased raw state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind) (RawCtxMixedOwner.receiveCost kind) := by
  rw [executeBeacon_exact, PqxdhBoundaryRecordPrelude.beacon_exact, isQueryBoundP_map_iff]
  exact RawCtxBeaconLifecycle.step_bound _ (.inr raw) _ _

end BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.owner_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.server_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.server_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.beacon_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.beacon_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.current_server_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.current_server_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.current_server_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordReceiveState.current_server_bounds
