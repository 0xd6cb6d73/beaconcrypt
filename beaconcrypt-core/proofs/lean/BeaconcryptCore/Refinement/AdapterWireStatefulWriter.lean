-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterWireRequestExtraction

/-! The source writer is interpreted as a request program rather than by fixing an allocator reply function. The interpretation returns the complete primitive state, including on allocator and serializer failure. The std vector operations remain the actual pinned CoreModels operations; their byte representation is handled separately. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterWireStatefulWriter
open AdapterWireRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)

@[instance_reducible] def rustOperations [operations : AdapterWirePrimitive.Operations] {T : Type}
    (serializer : AdapterWirePrimitive.Serializer T) (closure : T) :
    Operations operations.ReserveError RustM where
  reserve := alloc.vec.Vec.try_reserve_exact
  serialize input := serializer.call_once closure input

/-- Every source branch, std operation and mutable serializer result is retained by the lifting. -/
theorem body_specializes [operations : AdapterWirePrimitive.Operations] {T : Type}
    (serializer : AdapterWirePrimitive.Serializer T) (closure : T) (capacity : Usize) :
    @AdapterWireRequestExtraction.encodeRecord operations.ReserveError RustM _ _
      (rustOperations serializer closure) capacity =
      beaconcrypt.wire.encode_record serializer capacity closure := by
  rfl

def interpret {E A : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (work : Program E A) :
    OracleComp base (RustM A) := simulateQ impl work.run

@[simp] theorem interpret_lift {E A ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (value : RustM A) :
    interpret impl (liftRust value) = pure value := rfl

@[simp] theorem interpret_pure {E A ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (value : A) :
    interpret impl (pure value) = pure (.ok value) := rfl

theorem interpret_bind {E A B ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base))
    (work : Program E A) (next : A → Program E B) :
    interpret impl (work >>= next) = (do
      let result ← interpret impl work
      match result with
      | .ok value => interpret impl (next value)
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  change simulateQ impl (do
    let result ← work.run
    match result with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div) = _
  rw [simulateQ_bind]
  refine bind_congr fun result => ?_
  cases result <;> rfl

@[simp] theorem interpret_query {E ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (request : Request) :
    interpret impl (Program.query request) = impl request := by
  exact simulateQ_spec_query impl request

def execute {E σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base))) (capacity : Usize) :
    StateT σ (OracleComp base) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ impl (AdapterWireRequestExtraction.encodeRecord (E := E) (m := Program E) capacity).run

/-- Joint returned value and poststate are obtained from the source-derived request program, for arbitrary stateful and randomized allocator/serializer replies. -/
theorem source_stateful {E σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (capacity : Usize) (before : σ) :
    (execute impl capacity).run before =
      (simulateQ impl (AdapterWireRequestExtraction.encodeRecord (E := E) (m := Program E) capacity).run).run
        before := rfl

/-- Any later API callback starts from the actual writer poststate, including a failed reservation or failed serialization. -/
theorem source_continuation {E σ ι Output : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base))) (capacity : Usize)
    (next : RustM (core.option.Option (alloc.vec.Vec U8)) → StateT σ (OracleComp base) Output)
    (before : σ) :
    ((do let result ← execute impl capacity; next result).run before) = (do
      let result ← (execute impl capacity).run before
      (next result.1).run result.2) := by
  rw [StateT.run_bind]

end BeaconcryptCore.Refinement.AdapterWireStatefulWriter

/-- info: 'BeaconcryptCore.Refinement.AdapterWireStatefulWriter.body_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireStatefulWriter.body_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireStatefulWriter.interpret_query

/-- info: 'BeaconcryptCore.Refinement.AdapterWireStatefulWriter.source_stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireStatefulWriter.source_stateful

/-- info: 'BeaconcryptCore.Refinement.AdapterWireStatefulWriter.source_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireStatefulWriter.source_continuation
