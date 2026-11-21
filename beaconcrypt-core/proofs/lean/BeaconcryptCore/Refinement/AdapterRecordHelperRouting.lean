-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter
import BeaconcryptCore.Refinement.AdapterRecordRouting

/-! The selected production dispatcher carries exactly three chunks. Its source callbacks therefore instantiate the checked fixed-three helpers; callbacks outside this selected shape remain arbitrary and are never expanded. The stateful request dispatcher retains the same source constructor, sequence, sender and chunk order. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterRecordHelperRouting
open AdapterRecordHelperRequestMonad

@[instance_reducible] def sourceCallbacks [AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (other : RecordRoutingCallbacks.Operations) : RecordRoutingCallbacks.Operations where
  join {N} parts :=
    if three : N = 3#usize then
      beaconcrypt_record_helpers.ratchet._proof_join_record_three
        ⟨parts.val, by simpa only [three] using parts.property⟩
    else other.join parts
  frame sequence sender parts :=
    if three : parts.val.length = 3 then
      beaconcrypt_record_helpers.wire._proof_encode_frame_three sequence sender ⟨parts.val, three⟩
    else other.frame sequence sender parts

theorem source_raw [AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (other : RecordRoutingCallbacks.Operations) (parts : Array (Slice U8) 3#usize) :
    @beaconcrypt_record_routing.ratchet.execute_write_request (sourceCallbacks other) (.Raw parts) =
      beaconcrypt_record_helpers.ratchet._proof_join_record_three parts := by
  rfl

theorem source_frame [AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (other : RecordRoutingCallbacks.Operations) (sequence sender : U64) (parts : Array (Slice U8) 3#usize) :
    @beaconcrypt_record_routing.ratchet.execute_write_request (sourceCallbacks other) (.Frame parts sequence sender) =
      beaconcrypt_record_helpers.wire._proof_encode_frame_three sequence sender parts := by
  change (if three : parts.val.length = 3 then
    beaconcrypt_record_helpers.wire._proof_encode_frame_three sequence sender ⟨parts.val, three⟩
    else other.frame sequence sender (Array.to_slice parts)) = _
  split
  · rfl
  · exact False.elim (‹¬parts.val.length = 3› parts.property)

def route {E : Type} {m : Type → Type} [Monad m] [AdapterRecordRequestMonad.LiftRust m] [Operations E m]
    (request : record_effects.RecordWriteRequest) : m (core.option.Option (alloc.vec.Vec U8)) :=
  match request with
  | .Raw parts => AdapterRecordHelperRequestExtraction.raw (E := E) (m := m) parts
  | .Frame parts sequence sender => AdapterRecordHelperRequestExtraction.frame (E := E) (m := m) sequence sender parts

theorem route_specializes [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (other : RecordRoutingCallbacks.Operations) (request : record_effects.RecordWriteRequest) :
    @route allocator.ReserveError RustM _ _ AdapterRecordHelperStatefulWriter.rustOperations request =
      @beaconcrypt_record_routing.ratchet.execute_write_request (sourceCallbacks other) request := by
  cases request with
  | Raw parts =>
    exact (AdapterRecordHelperStatefulWriter.raw_specializes parts).trans (source_raw other parts).symm
  | Frame parts sequence sender =>
    exact (AdapterRecordHelperStatefulWriter.frame_specializes sequence sender parts).trans
      (source_frame other sequence sender parts).symm

def execute {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base))) (request : record_effects.RecordWriteRequest) :
    StateT σ (OracleComp base) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ implementation (route (E := E) (m := Program E) request).run

theorem execute_raw {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base))) (parts : Array (Slice U8) 3#usize) :
    execute implementation (.Raw parts) = AdapterRecordHelperStatefulWriter.raw implementation parts := rfl

theorem execute_frame {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (parts : Array (Slice U8) 3#usize) (sequence sender : U64) :
    execute implementation (.Frame parts sequence sender) =
      AdapterRecordHelperStatefulWriter.frame implementation sequence sender parts := rfl

theorem execute_continuation {E σ ι Output : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base))) (request : record_effects.RecordWriteRequest)
    (next : RustM (core.option.Option (alloc.vec.Vec U8)) → StateT σ (OracleComp base) Output) (before : σ) :
    ((do let result ← execute implementation request; next result).run before) = (do
      let result ← (execute implementation request).run before
      (next result.1).run result.2) := by
  rw [StateT.run_bind]
end BeaconcryptCore.Refinement.AdapterRecordHelperRouting

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRouting.source_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRouting.source_raw

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRouting.source_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRouting.source_frame

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRouting.route_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRouting.route_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRouting.execute_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRouting.execute_raw

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRouting.execute_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRouting.execute_frame

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRouting.execute_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRouting.execute_continuation
