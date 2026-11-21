-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordHelperRouting
import BeaconcryptCore.Refinement.AdapterOptionDeref

/-! The deployed record callback borrows the optional output Vec as a slice before resuming the source controller. This exact standard-library operation preserves the selected byte representation. Its stateful lifting retains every allocator/serializer state change and propagates enclosing RustM failure or divergence rather than replacing either with None. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterRecordNativeWriter

def borrow (result : RustM (core.option.Option (alloc.vec.Vec U8))) :
    RustM (core.option.Option (Slice U8)) := do
  let value ← result
  core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) value

theorem borrow_exact (result : RustM (core.option.Option (alloc.vec.Vec U8))) :
    borrow result = result := by
  cases result with
  | ok value => exact AdapterOptionDeref.byte_vector value
  | fail error => rfl
  | div => rfl

def write {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT σ (OracleComp base)))
    (request : record_effects.RecordWriteRequest) :
    StateT σ (OracleComp base) (RustM (core.option.Option (Slice U8))) :=
  borrow <$> AdapterRecordHelperRouting.execute implementation request

theorem write_exact {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT σ (OracleComp base)))
    (request : record_effects.RecordWriteRequest) :
    write implementation request = AdapterRecordHelperRouting.execute implementation request := by
  have same : borrow = (id : RustM (core.option.Option (alloc.vec.Vec U8)) →
      RustM (core.option.Option (alloc.vec.Vec U8))) := funext borrow_exact
  simp only [write, same, id_map]

theorem source [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]
    (other : RecordRoutingCallbacks.Operations) (request : record_effects.RecordWriteRequest) :
    borrow (@AdapterRecordHelperRouting.route allocator.ReserveError RustM _ _
      AdapterRecordHelperStatefulWriter.rustOperations request) = (do
      let value ← @beaconcrypt_record_routing.ratchet.execute_write_request
        (AdapterRecordHelperRouting.sourceCallbacks other) request
      core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) value) := by
  rw [AdapterRecordHelperRouting.route_specializes other]
  rfl

theorem write_joint {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT σ (OracleComp base)))
    (request : record_effects.RecordWriteRequest) (before : σ) :
    (write implementation request).run before =
      (AdapterRecordHelperRouting.execute implementation request).run before := by
  rw [write_exact]

theorem continuation {E σ ι Output : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT σ (OracleComp base)))
    (request : record_effects.RecordWriteRequest)
    (next : RustM (core.option.Option (Slice U8)) → StateT σ (OracleComp base) Output) (before : σ) :
    ((do let result ← write implementation request; next result).run before) = (do
      let result ← (AdapterRecordHelperRouting.execute implementation request).run before
      (next result.1).run result.2) := by
  rw [write_exact, StateT.run_bind]
  rfl

end BeaconcryptCore.Refinement.AdapterRecordNativeWriter

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeWriter.borrow_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeWriter.borrow_exact
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeWriter.write_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeWriter.write_exact
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeWriter.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeWriter.source
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeWriter.write_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeWriter.write_joint
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeWriter.continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeWriter.continuation
