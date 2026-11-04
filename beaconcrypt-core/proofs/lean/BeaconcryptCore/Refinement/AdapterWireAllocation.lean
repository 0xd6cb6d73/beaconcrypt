-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterWireVector

/-! The platform reservation contract exposes its complete ordinary result and preserves vector elements. It may fail, succeed on a later identical request, and update arbitrary shared state on either result. The serializer is also an arbitrary effect with its actual mutable buffer result. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterWireAllocation
open AdapterWireRequestMonad

variable {E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The std reservation leaf changes capacity, never initialized elements. Capacity itself is not observed by the selected source body. -/
def platform (reserve : Usize → m (core.result.Result Unit E))
    (serialize : Slice U8 → m (Usize × Slice U8)) : QueryImpl (Spec E) m
  | .reserve before capacity => (fun result => .ok (result, before)) <$> reserve capacity
  | .serialize input => .ok <$> serialize input

def encode (reserve : Usize → m (core.result.Result Unit E))
    (serialize : Slice U8 → m (Usize × Slice U8)) (capacity : Usize) :
    m (core.option.Option (alloc.vec.Vec U8)) := do
  let allocation ← reserve capacity
  match allocation with
  | .Err _ => return .None
  | .Ok _ =>
    let (written, output) ← serialize (AdapterWireVector.zeros capacity)
    return if written = 0#usize then .None else .Some (AdapterWireVector.take output written)

set_option backward.isDefEq.respectTransparency false in
theorem source (reserve : Usize → m (core.result.Result Unit E))
    (serialize : Slice U8 → m (Usize × Slice U8)) (capacity : Usize) :
    simulateQ (platform reserve serialize)
        (AdapterWireRequestExtraction.encodeRecord (E := E) (m := Program E) capacity).run =
      .ok <$> encode reserve serialize capacity := by
  simp! only [AdapterWireRequestExtraction.encodeRecord, Lifted.new,
    alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, bind_tc_ok,
    Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
    Operations.reserve, Operations.serialize, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, pure_bind, platform, bind_map_left, encode, map_bind]
  refine bind_congr fun allocation => ?_
  cases allocation with
  | Err error =>
      simp! only [Lifted.resultOk, Lifted.branch, Lifted.fromResidual,
        core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
        Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure,
        bind_tc_ok, pure_bind, map_pure]
  | Ok value =>
      simp! only [Lifted.resultOk, Lifted.branch, Lifted.resize, Lifted.derefMut,
        core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        AdapterWireVector.resize_empty, AdapterWireVector.deref_mut_bytes,
        Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure,
        bind_tc_ok, pure_bind, Program.query, simulateQ_spec_query, platform, bind_map_left, map_bind]
      refine bind_congr fun result => ?_
      rcases result with ⟨written, output⟩
      split <;> simp only [Lifted.truncate, AdapterWireVector.truncate_bytes,
        Program.run_bind, Program.run_lift, Program.run_pure,
        simulateQ_pure, pure_bind, map_pure, id_eq]

end BeaconcryptCore.Refinement.AdapterWireAllocation

/-- info: 'BeaconcryptCore.Refinement.AdapterWireAllocation.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireAllocation.source
