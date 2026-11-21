-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRegistrationWriterRequestExtraction
import BeaconcryptCore.Refinement.AdapterWireAllocation
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact allocation-body interpretation with a complete RustM buffer serializer. Reservation keeps initialized vector elements and may change arbitrary shared state, including on failure. No allocation success premise is supplied. -/
namespace BeaconcryptCore.Refinement.RegistrationSourceWriterBody
open AdapterRegistrationWriterRequestMonad
variable {E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def platform (reserve : Usize → m (core.result.Result Unit E))
    (encodeInit : beaconcrypt_parse.transport.initkex → Slice U8 → RustM (Usize × Slice U8))
    (encodeResponse : beaconcrypt_parse.transport.kexresponse → Slice U8 → RustM (Usize × Slice U8)) :
    QueryImpl (Spec E) m
  | .reserve before capacity => (fun result => .ok (result, before)) <$> reserve capacity
  | .encodeInit packet input => pure (encodeInit packet input)
  | .encodeResponse packet input => pure (encodeResponse packet input)

def reply (allocation : core.result.Result Unit E) (written : Usize) (output : Slice U8) :
    RustM (core.option.Option (alloc.vec.Vec U8)) :=
  .ok (match allocation with
    | .Err _ => .None
    | .Ok _ => if written = 0#usize then .None else .Some (AdapterWireVector.take output written))

set_option backward.isDefEq.respectTransparency false in
theorem init (reserve : Usize → m (core.result.Result Unit E))
    (encodeInit : beaconcrypt_parse.transport.initkex → Slice U8 → RustM (Usize × Slice U8))
    (encodeResponse : beaconcrypt_parse.transport.kexresponse → Slice U8 → RustM (Usize × Slice U8))
    (capacity written : Usize) (packet : beaconcrypt_parse.transport.initkex) (output : Slice U8)
    (serialized : encodeInit packet (AdapterWireVector.zeros capacity) = .ok (written, output)) :
    simulateQ (platform reserve encodeInit encodeResponse)
      (Lifted.writeInit (E := E) (m := Program E) capacity packet).run =
      (fun allocation => reply allocation written output) <$> reserve capacity := by
  simp! only [Lifted.writeInit, AdapterWireRequestExtraction.encodeRecord,
    AdapterWireRequestMonad.Lifted.new, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
    bind_tc_ok, Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
    AdapterWireRequestMonad.Operations.reserve, Operations.reserve,
    simulateQ_bind, simulateQ_pure, simulateQ_spec_query, pure_bind,
    platform, bind_map_left, map_bind]
  rw [← bind_pure_comp]
  refine bind_congr (m := m) fun allocation => ?_
  cases allocation with
  | Err error =>
    simp! only [AdapterWireRequestMonad.Lifted.resultOk, AdapterWireRequestMonad.Lifted.branch,
      AdapterWireRequestMonad.Lifted.fromResidual, core.result.Result.ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure,
      bind_tc_ok, pure_bind, map_pure, reply]
  | Ok value =>
    simp! only [AdapterWireRequestMonad.Lifted.resultOk, AdapterWireRequestMonad.Lifted.branch,
      AdapterWireRequestMonad.Lifted.resize, AdapterWireRequestMonad.Lifted.derefMut,
      core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      AdapterWireVector.resize_empty, AdapterWireVector.deref_mut_bytes,
      Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure,
      bind_tc_ok, pure_bind, Program.query, simulateQ_spec_query, platform,
      AdapterWireRequestMonad.Operations.serialize, Operations.encodeInit,
      serialized, reply]
    split <;> simp only [AdapterWireRequestMonad.Lifted.truncate, AdapterWireVector.truncate_bytes,
      Program.run_bind, Program.run_lift, Program.run_pure, simulateQ_pure,
      pure_bind, id_eq]
set_option backward.isDefEq.respectTransparency false in
theorem response (reserve : Usize → m (core.result.Result Unit E))
    (encodeInit : beaconcrypt_parse.transport.initkex → Slice U8 → RustM (Usize × Slice U8))
    (encodeResponse : beaconcrypt_parse.transport.kexresponse → Slice U8 → RustM (Usize × Slice U8))
    (capacity written : Usize) (packet : beaconcrypt_parse.transport.kexresponse) (output : Slice U8)
    (serialized : encodeResponse packet (AdapterWireVector.zeros capacity) = .ok (written, output)) :
    simulateQ (platform reserve encodeInit encodeResponse)
      (Lifted.writeResponse (E := E) (m := Program E) capacity packet).run =
      (fun allocation => reply allocation written output) <$> reserve capacity := by
  simp! only [Lifted.writeResponse, AdapterWireRequestExtraction.encodeRecord,
    AdapterWireRequestMonad.Lifted.new, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
    bind_tc_ok, Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
    AdapterWireRequestMonad.Operations.reserve, Operations.reserve,
    simulateQ_bind, simulateQ_pure, simulateQ_spec_query, pure_bind,
    platform, bind_map_left, map_bind]
  rw [← bind_pure_comp]
  refine bind_congr (m := m) fun allocation => ?_
  cases allocation with
  | Err error =>
    simp! only [AdapterWireRequestMonad.Lifted.resultOk, AdapterWireRequestMonad.Lifted.branch,
      AdapterWireRequestMonad.Lifted.fromResidual, core.result.Result.ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure,
      bind_tc_ok, pure_bind, map_pure, reply]
  | Ok value =>
    simp! only [AdapterWireRequestMonad.Lifted.resultOk, AdapterWireRequestMonad.Lifted.branch,
      AdapterWireRequestMonad.Lifted.resize, AdapterWireRequestMonad.Lifted.derefMut,
      core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      AdapterWireVector.resize_empty, AdapterWireVector.deref_mut_bytes,
      Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure,
      bind_tc_ok, pure_bind, Program.query, simulateQ_spec_query, platform,
      AdapterWireRequestMonad.Operations.serialize, Operations.encodeResponse,
      serialized, reply]
    split <;> simp only [AdapterWireRequestMonad.Lifted.truncate, AdapterWireVector.truncate_bytes,
      Program.run_bind, Program.run_lift, Program.run_pure, simulateQ_pure,
      pure_bind, id_eq]
end BeaconcryptCore.Refinement.RegistrationSourceWriterBody

/-- info: 'BeaconcryptCore.Refinement.RegistrationSourceWriterBody.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSourceWriterBody.init

/-- info: 'BeaconcryptCore.Refinement.RegistrationSourceWriterBody.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSourceWriterBody.response
