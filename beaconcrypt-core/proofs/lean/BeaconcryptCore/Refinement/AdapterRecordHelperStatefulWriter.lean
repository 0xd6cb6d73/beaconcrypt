-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordHelperRequestExtraction
import BeaconcryptCore.Refinement.FrameDispatch

/-! The actual selected raw join and three-part frame helper specialize from their checked request lifts. Shared allocator/serializer state is retained on all outcomes, including rejected capacity, reservation error, mutable serialization failure, Rust failure and divergence. Later callbacks continue from the actual reached poststate. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter
open AdapterRecordHelperRequestMonad

@[instance_reducible] def rustOperations [allocator : AdapterWirePrimitive.Operations]
    [FrameDispatchFallback.Operations] : Operations allocator.ReserveError RustM where
  reserve := alloc.vec.Vec.try_reserve_exact
  encodeFrame sequence sender parts input :=
    beaconcrypt_record_helpers.wire._proof_encode_frame_three.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
      (sequence, sender, parts) input

theorem frame_specializes [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (sequence sender : U64) (parts : Array (Slice U8) 3#usize) :
    @AdapterRecordHelperRequestExtraction.frame allocator.ReserveError RustM _ _ rustOperations sequence sender parts =
      beaconcrypt_record_helpers.wire._proof_encode_frame_three sequence sender parts := by
  rfl

theorem raw_specializes [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (parts : Array (Slice U8) 3#usize) :
    @AdapterRecordHelperRequestExtraction.raw allocator.ReserveError RustM _ _ rustOperations parts =
      beaconcrypt_record_helpers.ratchet._proof_join_record_three parts := by
  rfl

theorem serializer_selected [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (sequence sender : U64) (parts : Array (Slice U8) 3#usize) (output : Slice U8) :
    ∃ first second third, parts.val = [first, second, third] ∧
      (rustOperations.encodeFrame sequence sender parts output) =
        beaconcrypt_parse.frame.encode_three sequence sender first second third output := by
  obtain ⟨first, second, third, same, selected⟩ := FrameDispatch.selected_array sequence sender parts output
  refine ⟨first, second, third, congrArg Subtype.val same, ?_⟩
  exact selected

def interpret {E A ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (work : Program E A) :
    OracleComp base (RustM A) := simulateQ implementation work.run

@[simp] theorem interpret_pure {E A ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (value : A) :
    interpret implementation (pure value) = pure (.ok value) := rfl

@[simp] theorem interpret_lift {E A ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (value : RustM A) :
    interpret implementation (AdapterRecordRequestMonad.liftRust value) = pure value := rfl

theorem interpret_bind {E A B ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base))
    (work : Program E A) (next : A → Program E B) :
    interpret implementation (work >>= next) = (do
      let result ← interpret implementation work
      match result with
      | .ok value => interpret implementation (next value)
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  change simulateQ implementation (do
    let result ← work.run
    match result with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div) = _
  rw [simulateQ_bind]
  refine bind_congr fun result => ?_
  cases result <;> rfl

@[simp] theorem interpret_query {E ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (request : Request) :
    interpret implementation (Program.query request) = implementation request :=
  simulateQ_spec_query implementation request

def raw {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (parts : Array (Slice U8) 3#usize) :
    StateT σ (OracleComp base) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ implementation (AdapterRecordHelperRequestExtraction.raw (E := E) (m := Program E) parts).run

def frame {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (sequence sender : U64) (parts : Array (Slice U8) 3#usize) :
    StateT σ (OracleComp base) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ implementation (AdapterRecordHelperRequestExtraction.frame (E := E) (m := Program E) sequence sender parts).run

theorem raw_joint {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (parts : Array (Slice U8) 3#usize) (before : σ) :
    (raw implementation parts).run before =
      (simulateQ implementation (AdapterRecordHelperRequestExtraction.raw
        (E := E) (m := Program E) parts).run).run before := rfl

theorem frame_joint {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (sequence sender : U64) (parts : Array (Slice U8) 3#usize) (before : σ) :
    (frame implementation sequence sender parts).run before =
      (simulateQ implementation (AdapterRecordHelperRequestExtraction.frame
        (E := E) (m := Program E) sequence sender parts).run).run before := rfl

theorem raw_continuation {E σ ι Output : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (parts : Array (Slice U8) 3#usize)
    (next : RustM (core.option.Option (alloc.vec.Vec U8)) → StateT σ (OracleComp base) Output) (before : σ) :
    ((do let result ← raw implementation parts; next result).run before) = (do
      let result ← (raw implementation parts).run before
      (next result.1).run result.2) := by
  rw [StateT.run_bind]

theorem frame_continuation {E σ ι Output : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (sequence sender : U64) (parts : Array (Slice U8) 3#usize)
    (next : RustM (core.option.Option (alloc.vec.Vec U8)) → StateT σ (OracleComp base) Output) (before : σ) :
    ((do let result ← frame implementation sequence sender parts; next result).run before) = (do
      let result ← (frame implementation sequence sender parts).run before
      (next result.1).run result.2) := by
  rw [StateT.run_bind]

theorem raw_source [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    {σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec allocator.ReserveError) (StateT σ (OracleComp base)))
    (parts : Array (Slice U8) 3#usize) (before : σ) :
    (@AdapterRecordHelperRequestExtraction.raw allocator.ReserveError RustM _ _ rustOperations parts =
      beaconcrypt_record_helpers.ratchet._proof_join_record_three parts) ∧
    ((raw implementation parts).run before =
      (simulateQ implementation (AdapterRecordHelperRequestExtraction.raw
        (E := allocator.ReserveError) (m := Program allocator.ReserveError) parts).run).run before) :=
  ⟨raw_specializes parts, raw_joint implementation parts before⟩

theorem frame_source [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    {σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec allocator.ReserveError) (StateT σ (OracleComp base)))
    (sequence sender : U64) (parts : Array (Slice U8) 3#usize) (before : σ) :
    (@AdapterRecordHelperRequestExtraction.frame allocator.ReserveError RustM _ _ rustOperations sequence sender parts =
      beaconcrypt_record_helpers.wire._proof_encode_frame_three sequence sender parts) ∧
    ((frame implementation sequence sender parts).run before =
      (simulateQ implementation (AdapterRecordHelperRequestExtraction.frame
        (E := allocator.ReserveError) (m := Program allocator.ReserveError) sequence sender parts).run).run before) :=
  ⟨frame_specializes sequence sender parts, frame_joint implementation sequence sender parts before⟩
end BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.serializer_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.serializer_selected

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.interpret_query

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_joint

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_joint

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_continuation

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_continuation

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.raw_source

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperStatefulWriter.frame_source
