-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterWireAllocation
import BeaconcryptCore.Computational.RegistrationNativeAllocation

/-! Exact byte projection of the selected extracted writer. Standard reservation preserves initialized vector elements, but its success/error reply and every allocator poststate remain in the execution. The source serializer receives the actual zero-initialized buffer. -/
open CoreModels Aeneas OracleComp
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation
open BeaconcryptCore.Refinement

def bytes (value : alloc.vec.Vec U8) : Pqxdh.Bytes := value.val.map PqxdhRefinement.absByte

def output (value : core.option.Option (alloc.vec.Vec U8)) : Option Pqxdh.Bytes :=
  Option.map bytes value

def succeeded {E : Type} : core.result.Result Unit E → Bool
  | .Ok _ => true
  | .Err _ => false

theorem truncate_projection (value : alloc.vec.Vec U8) (written : Usize) :
    bytes (AdapterWireVector.take value written) = (bytes value).take written.val := by
  exact List.map_take

theorem zeros_projection (capacity : Usize) :
    bytes (AdapterWireVector.zeros capacity) = List.replicate capacity.val 0 := by
  simp only [bytes, AdapterWireVector.zeros, List.map_replicate]
  rfl

variable {E σ : Type}

set_option backward.isDefEq.respectTransparency false in
/-- The native allocation semantics is the exact byte abstraction of the original writer, including nonzero over-reports handled by std truncation. -/
theorem allocation_projection
    (reserve : Usize → StateT σ ProbComp (core.result.Result Unit E))
    (serialize : Slice U8 → StateT σ ProbComp (Usize × Slice U8))
    (capacity : Usize) :
    output <$> AdapterWireAllocation.encode reserve serialize capacity =
      RegistrationNativeAllocation.encodeRecord
        (fun _ => succeeded <$> reserve capacity)
        (fun _ => (fun result => (result.1.val, bytes result.2)) <$>
          serialize (AdapterWireVector.zeros capacity)) capacity.val := by
  simp only [AdapterWireAllocation.encode, RegistrationNativeAllocation.encodeRecord,
    map_bind, bind_map_left]
  refine bind_congr fun allocation => ?_
  cases allocation with
  | Err error => rfl
  | Ok value =>
      simp only [succeeded, Bool.not_true, Bool.false_eq_true, ite_false, map_bind]
      refine bind_congr fun result => ?_
      rcases result with ⟨written, buffer⟩
      simp only [map_pure, output]
      by_cases empty : written = 0#usize
      · have emptyVal : written.val = 0 := by
          simpa only [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] using empty
        simp only [empty, UScalar.ofNatCore_val_eq, ite_true, Option.map_none]
      · have nonemptyVal : ¬ written.val = 0 := by
          simpa only [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] using empty
        simp only [empty, nonemptyVal, ite_false, Option.map_some, truncate_projection]

def abstractResult : RustM (core.option.Option (alloc.vec.Vec U8)) →
    RustM (Option Pqxdh.Bytes)
  | .ok value => .ok (output value)
  | .fail error => .fail error
  | .div => .div

theorem source_projection
    (reserve : Usize → StateT σ ProbComp (core.result.Result Unit E))
    (serialize : Slice U8 → StateT σ ProbComp (Usize × Slice U8))
    (capacity : Usize) :
    abstractResult <$> simulateQ (AdapterWireAllocation.platform reserve serialize)
        (AdapterWireRequestExtraction.encodeRecord (E := E)
          (m := AdapterWireRequestMonad.Program E) capacity).run =
      .ok <$> RegistrationNativeAllocation.encodeRecord
        (fun _ => succeeded <$> reserve capacity)
        (fun _ => (fun result => (result.1.val, bytes result.2)) <$>
          serialize (AdapterWireVector.zeros capacity)) capacity.val := by
  rw [AdapterWireAllocation.source]
  simpa only [Functor.map_map, abstractResult] using
    congrArg (fun work : StateT σ ProbComp (Option Pqxdh.Bytes) =>
      (RustM.ok : Option Pqxdh.Bytes → RustM (Option Pqxdh.Bytes)) <$> work)
      (allocation_projection reserve serialize capacity)

/-- The actual source program has this complete joint output/poststate distribution, with no successful-allocation premise. -/
theorem source_joint
    (reserve : Usize → StateT σ ProbComp (core.result.Result Unit E))
    (serialize : Slice U8 → StateT σ ProbComp (Usize × Slice U8))
    (capacity : Usize) (before : σ) :
    (fun result => (abstractResult result.1, result.2)) <$>
        (AdapterWireStatefulWriter.execute
          (AdapterWireAllocation.platform reserve serialize) capacity).run before =
      (fun result => (.ok result.1, result.2)) <$>
        (RegistrationNativeAllocation.encodeRecord
          (fun _ => succeeded <$> reserve capacity)
          (fun _ => (fun result => (result.1.val, bytes result.2)) <$>
            serialize (AdapterWireVector.zeros capacity)) capacity.val).run before := by
  simpa only [StateT.run_map, AdapterWireStatefulWriter.execute] using
    congrArg (fun work => work.run before) (source_projection reserve serialize capacity)

end BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.truncate_projection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.truncate_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.zeros_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.zeros_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.allocation_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.allocation_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.source_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.source_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation.source_joint
