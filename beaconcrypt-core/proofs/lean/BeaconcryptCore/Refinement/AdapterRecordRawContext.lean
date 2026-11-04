-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation
import BeaconcryptCore.Computational.CborProductionBoundary

/-! The unchanged typed native frame parser surrounds the actual extracted receive controller. This context theorem preserves empty/oversized/malformed rejection, sender checking, the whole kernel and every primitive effect. The parser is the same functional parameter on both sides; proving its concrete Rust correspondence is a separate codec obligation. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRecordRawContext
open BeaconcryptCore.Computational
open PqxdhRefinement
variable {PrimitiveState Metadata : Type}

/-- Only the outer model's functional parser is reused; its result already contains the original bounded payload slice. -/
def parsed (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (raw : Pqxdh.Bytes) :=
  if raw.length ≤ CborSizing.maxMessageSize then parse raw else none

theorem parsed_decoded (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (raw : Pqxdh.Bytes) :
    CborProductionBoundary.decoded <$> parsed parse raw = CborProductionBoundary.frameDecoder parse raw := by
  simp only [parsed, CborProductionBoundary.frameDecoder, CborTransport.boundedDecoder]
  split <;> rfl

/-- This projection is used only after the exact source theorem proves a normal core return. Optional cryptographic failure remains inside that normal value. -/
def result (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (value : RustM RecordEffectsReceiveProgram.Result) : RecordEffectsReceiveProgram.Result :=
  match value with
  | .ok value => value
  | .fail _ | .div => (kernel, none)

noncomputable def afterDecode
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (erased : Array Std.U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (expected : Std.U64) (frame : CborProductionBoundary.NativeFrame) (ad : Array Std.U8 281#usize) :
    StateT PrimitiveState ProbComp (RustM RecordEffectsReceiveProgram.Result) :=
  if frame.sender = expected then
    AdapterRecordNativeRepresentation.receive impl erased kernel frame.sequence frame.payload ad frame.sender
  else pure (.ok (kernel, none))

/-- The parsed typed payload and AD supply the exact original receive context without an assumed parser law. -/
theorem afterDecode_native
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (functional : AdapterRecordNativeRepresentation.Functional impl)
    (erased : Array Std.U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (expected : Std.U64) (raw : Pqxdh.Bytes) (frame : CborProductionBoundary.NativeFrame)
    (ad : Array Std.U8 281#usize) (before : PrimitiveState) :
    (afterDecode impl erased kernel expected frame ad).run before =
      (simulateQ impl ((fun result => .ok result) <$> simulateQ RawCtxSourceOpen.nativeAdapter
        (if RawCtxReceive.ValidFrame expected (absBytes ad) (CborProductionBoundary.decoded frame) then
          simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
              ⟨raw, CborProductionBoundary.decoded frame, absBytes ad⟩)
        else pure (kernel, none)))).run before := by
  have source : (afterDecode impl erased kernel expected frame ad).run before =
      (simulateQ impl (RecordEffectsReceiveProgram.decoded erased kernel expected
        (CborProductionBoundary.decoded frame) frame.payload ad)).run before := by
    unfold afterDecode RecordEffectsReceiveProgram.decoded CborProductionBoundary.decoded
    split
    · exact AdapterRecordNativeRepresentation.receive_native impl functional erased kernel frame.sequence frame.payload ad frame.sender before
    · rfl
  rw [source, RecordEffectsReceiveBridge.decoded_native_model erased kernel expected raw
    (CborProductionBoundary.decoded frame) (absBytes ad) frame.payload ad rfl rfl]
  rfl

/-- The source-selected raw operation retains the original literal parser order and reinstalls one complete returned kernel. -/
noncomputable def raw
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (erased : Array Std.U8 357#usize)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (ad : Array Std.U8 281#usize) (bytes : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata) :
    StateT PrimitiveState ProbComp (Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) :=
  if bytes.isEmpty then pure (RawCtxWholeOwner.publish state (state.owner.kernel, none))
  else match parsed parse bytes with
  | none => pure (RawCtxWholeOwner.publish state (state.owner.kernel, none))
  | some frame => do
      let reply ← afterDecode impl erased state.owner.kernel state.owner.expectedSender frame ad
      pure (RawCtxWholeOwner.publish state (result state.owner.kernel reply))

/-- The actual source loop occupies the original raw-owner context, preserving the full owner and primitive state through all rejection and failure histories. -/
theorem raw_native
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (functional : AdapterRecordNativeRepresentation.Functional impl)
    (erased : Array Std.U8 357#usize)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (ad : Array Std.U8 281#usize) (bytes : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (represented : state.owner.associatedData = absBytes ad)
    (before : PrimitiveState) :
    (raw impl erased parse ad bytes state).run before =
      (simulateQ impl (simulateQ RawCtxSourceOpen.nativeAdapter
        ((RawCtxWholeOwner.rawReceive (CborProductionBoundary.frameDecoder parse) bytes).run state))).run before := by
  unfold raw RawCtxWholeOwner.rawReceive
  split
  · rfl
  · simp only [StateT.run, ← parsed_decoded]
    cases reading : parsed parse bytes with
    | none => rfl
    | some frame =>
        change (do
          let reply ← (afterDecode impl erased state.owner.kernel state.owner.expectedSender frame ad).run before
          pure (RawCtxWholeOwner.publish state (result state.owner.kernel reply.1), reply.2)) =
          (simulateQ impl (simulateQ RawCtxSourceOpen.nativeAdapter
            (if RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData
                (CborProductionBoundary.decoded frame) then do
              let value ← simulateQ RawCtxWholeOwner.adapter
                (RawCtxOwnerOracle.receive state.owner.kernel frame.sequence
                  ⟨bytes, CborProductionBoundary.decoded frame, state.owner.associatedData⟩)
              pure (RawCtxWholeOwner.publish state value)
            else pure (RawCtxWholeOwner.publish state (state.owner.kernel, none))))).run before
        rw [afterDecode_native impl functional erased state.owner.kernel state.owner.expectedSender bytes frame ad before]
        simp only [represented]
        by_cases valid : RawCtxReceive.ValidFrame state.owner.expectedSender (absBytes ad)
          (CborProductionBoundary.decoded frame)
        all_goals simp only [valid, ite_true, ite_false, simulateQ_map, StateT.run_map,
          simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          bind_map_left, result, pure_bind]

end BeaconcryptCore.Refinement.AdapterRecordRawContext

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRawContext.parsed_decoded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRawContext.parsed_decoded

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRawContext.afterDecode_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRawContext.afterDecode_native

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRawContext.raw_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRawContext.raw_native
