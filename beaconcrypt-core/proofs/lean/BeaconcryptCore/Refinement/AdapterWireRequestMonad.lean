-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterWireExtraction.Funs
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad

/-! Request interpretation of the selected source writer. Reservation and the mutable serializer remain distinct effects. A failed reservation returns its updated allocator state and does not invoke the serializer. Rust failure and divergence remain short circuiting outcomes. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterWireRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)

class Operations (E : Type) (m : Type → Type) where
  reserve : alloc.vec.Vec U8 → Usize → m (core.result.Result Unit E × alloc.vec.Vec U8)
  serialize : Slice U8 → m (Usize × Slice U8)

namespace Lifted
variable {m : Type → Type} [LiftRust m]

def new : m (alloc.vec.Vec U8) := liftRust (alloc.vec.Vec.new U8)
def resultOk {E : Type} (result : core.result.Result Unit E) :=
  liftRust (core.result.Result.ok result) (m := m)
def branch (result : core.option.Option Unit) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch result) (m := m)
def resize (before : alloc.vec.Vec U8) (capacity : Usize) :=
  liftRust (alloc.vec.Vec.resize core.U8.Insts.CoreCloneClone before capacity 0#u8) (m := m)
def derefMut (before : alloc.vec.Vec U8) :=
  liftRust (alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut before) (m := m)
def truncate (before : alloc.vec.Vec U8) (written : Usize) :=
  liftRust (alloc.vec.Vec.truncate before written) (m := m)
def fromResidual (residual : core.option.Option core.convert.Infallible) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (alloc.vec.Vec U8) residual) (m := m)
end Lifted

inductive Request where
  | reserve (before : alloc.vec.Vec U8) (capacity : Usize)
  | serialize (input : Slice U8)

abbrev Response (E : Type) : Request → Type
  | .reserve _ _ => core.result.Result Unit E × alloc.vec.Vec U8
  | .serialize _ => Usize × Slice U8

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

def query (request : Request) : Program E (Response E request) :=
  ⟨OracleComp.lift ((Spec E).query request)⟩

instance : Operations E (Program E) where
  reserve before capacity := query (.reserve before capacity)
  serialize input := query (.serialize input)

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
    intro A B C work next last
    apply ext
    simp only [run_bind, bind_assoc]
    refine bind_congr fun result => ?_
    cases result <;> simp only [pure_bind])

end Program
end BeaconcryptCore.Refinement.AdapterWireRequestMonad

/-- info: 'BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.run_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.run_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.run_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.ext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireRequestMonad.Program.ext
