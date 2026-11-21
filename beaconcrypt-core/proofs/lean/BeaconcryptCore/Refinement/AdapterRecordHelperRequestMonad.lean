-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordHelpersExtraction.Funs
import BeaconcryptCore.AdapterWireRequestExtraction
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad

/-! Requests for the actual fixed-three-part raw join and ordinary frame writer. The source length checks and std vector operations stay lifted RustM computations. Reservation and the complete mutable frame serializer are separate effects; ordinary None, Rust failure and divergence remain distinct. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)

class Operations (E : Type) (m : Type → Type) where
  reserve : alloc.vec.Vec U8 → Usize → m (core.result.Result Unit E × alloc.vec.Vec U8)
  encodeFrame : U64 → U64 → Array (Slice U8) 3#usize → Slice U8 → m (Usize × Slice U8)

namespace Lifted
variable {m : Type → Type} [LiftRust m]
def index (parts : Array (Slice U8) 3#usize) (position : Usize) := liftRust (Array.index_usize parts position) (m := m)
def len (input : Slice U8) := liftRust (core.slice.Slice.len input) (m := m)
def checkedAdd (left right : Usize) := liftRust (core.num.Usize.checked_add left right) (m := m)
def branch {A : Type} (value : core.option.Option A) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch value) (m := m)
def fromResidual (value : core.option.Option core.convert.Infallible) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual (alloc.vec.Vec U8) value) (m := m)
def new := liftRust (alloc.vec.Vec.new U8) (m := m)
def resultOk {E : Type} (value : core.result.Result Unit E) := liftRust (core.result.Result.ok value) (m := m)
def extend (before : alloc.vec.Vec U8) (input : Slice U8) :=
  liftRust (alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone before input) (m := m)
def frameCapacity (sequence sender : U64) (length : Usize) :=
  liftRust (beaconcrypt_core.transport.encoded_frame_len sequence sender length) (m := m)

variable {E : Type} [Monad m] [ops : Operations E m]
def writeFrame (capacity : Usize) (sequence sender : U64) (parts : Array (Slice U8) 3#usize) :
    m (core.option.Option (alloc.vec.Vec U8)) :=
  let _ : AdapterWireRequestMonad.Operations E m := ⟨ops.reserve, ops.encodeFrame sequence sender parts⟩
  AdapterWireRequestExtraction.encodeRecord (E := E) capacity
end Lifted

inductive Request where
  | reserve (before : alloc.vec.Vec U8) (capacity : Usize)
  | encodeFrame (sequence sender : U64) (parts : Array (Slice U8) 3#usize) (input : Slice U8)

abbrev Response (E : Type) : Request → Type
  | .reserve _ _ => core.result.Result Unit E × alloc.vec.Vec U8
  | .encodeFrame _ _ _ _ => Usize × Slice U8
abbrev Spec (E : Type) : OracleSpec Request := fun request => RustM (Response E request)

structure Program (E : Type) (A : Type) where
  run : OracleComp (Spec E) (RustM A)

namespace Program
variable {E A B C : Type}
def pure (value : A) : Program E A := ⟨Pure.pure (.ok value)⟩
def bind (work : Program E A) (next : A → Program E B) : Program E B := ⟨do
  let result ← work.run
  match result with
  | .ok value => (next value).run
  | .fail error => Pure.pure (.fail error)
  | .div => Pure.pure .div⟩
instance : Monad (Program E) where
  pure := pure
  bind := bind
instance : LiftRust (Program E) where
  liftRust value := ⟨Pure.pure value⟩
def query (request : Request) : Program E (Response E request) := ⟨(Spec E).query request⟩
instance : Operations E (Program E) where
  reserve before capacity := query (.reserve before capacity)
  encodeFrame sequence sender parts input := query (.encodeFrame sequence sender parts input)

@[simp] theorem run_pure (value : A) :
    (Pure.pure value : Program E A).run = Pure.pure (.ok value) := rfl
@[simp] theorem run_lift (value : RustM A) :
    (liftRust value : Program E A).run = Pure.pure value := rfl
@[simp] theorem run_bind (work : Program E A) (next : A → Program E B) :
    (work >>= next).run = (do
      let result ← work.run
      match result with
      | .ok value => (next value).run
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) := rfl
theorem ext (left right : Program E A) (same : left.run = right.run) : left = right := by
  cases left
  cases right
  cases same
  rfl
instance : LawfulMonad (Program E) := LawfulMonad.mk' (Program E)
  (by
    intro A work
    apply ext
    change (work.run >>= fun result => match result with
      | .ok value => Pure.pure (.ok value)
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) = work.run
    have same : (fun result : RustM A => match result with
        | .ok value => Pure.pure (.ok value)
        | .fail error => Pure.pure (.fail error)
        | .div => Pure.pure .div) = (Pure.pure : RustM A → OracleComp (Spec E) (RustM A)) := by
      funext result
      cases result <;> rfl
    rw [same, bind_pure])
  (by intros; rfl)
  (by
    intros
    apply ext
    simp only [run_bind, bind_assoc]
    refine bind_congr fun result => ?_
    cases result <;> simp only [pure_bind])
end Program
end BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.run_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program.ext
