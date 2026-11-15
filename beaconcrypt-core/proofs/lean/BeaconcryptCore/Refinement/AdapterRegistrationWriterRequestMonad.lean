-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRegistrationWriterExtraction.Funs
import BeaconcryptCore.AdapterWireRequestExtraction
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad

/-! Source-derived registration writer requests retain the actual packet and mutable serializer poststate. Reservation is distinct from both schema serializers. The common allocation body is the existing source-derived writer program. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)

class Operations (E : Type) (m : Type → Type) where
  reserve : alloc.vec.Vec U8 → Usize → m (core.result.Result Unit E × alloc.vec.Vec U8)
  encodeInit : beaconcrypt_parse.transport.initkex → Slice U8 → m (Usize × Slice U8)
  encodeResponse : beaconcrypt_parse.transport.kexresponse → Slice U8 → m (Usize × Slice U8)

namespace Lifted
variable {E : Type} {m : Type → Type} [Monad m] [LiftRust m] [ops : Operations E m]
def len (input : Slice U8) : m Usize := liftRust (core.slice.Slice.len input)
def initCapacity (lengths : Array Usize 4#usize) := liftRust (beaconcrypt_core.transport.encoded_init_len lengths) (m := m)
def responseCapacity (lengths : Array Usize 5#usize) (keyId : U64) := liftRust (beaconcrypt_core.transport.encoded_response_len lengths keyId) (m := m)
def branch (input : core.option.Option Usize) := liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch input) (m := m)
def fromResidual (residual : core.option.Option core.convert.Infallible) := liftRust (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual (alloc.vec.Vec U8) residual) (m := m)
def writeInit (capacity : Usize) (packet : beaconcrypt_parse.transport.initkex) : m (core.option.Option (alloc.vec.Vec U8)) :=
  let _ : AdapterWireRequestMonad.Operations E m := ⟨ops.reserve, ops.encodeInit packet⟩
  AdapterWireRequestExtraction.encodeRecord (E := E) capacity
def writeResponse (capacity : Usize) (packet : beaconcrypt_parse.transport.kexresponse) : m (core.option.Option (alloc.vec.Vec U8)) :=
  let _ : AdapterWireRequestMonad.Operations E m := ⟨ops.reserve, ops.encodeResponse packet⟩
  AdapterWireRequestExtraction.encodeRecord (E := E) capacity
end Lifted

inductive Request where
  | reserve (before : alloc.vec.Vec U8) (capacity : Usize)
  | encodeInit (packet : beaconcrypt_parse.transport.initkex) (input : Slice U8)
  | encodeResponse (packet : beaconcrypt_parse.transport.kexresponse) (input : Slice U8)

abbrev Response (E : Type) : Request → Type
  | .reserve _ _ => core.result.Result Unit E × alloc.vec.Vec U8
  | .encodeInit _ _ | .encodeResponse _ _ => Usize × Slice U8

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
  encodeInit packet input := query (.encodeInit packet input)
  encodeResponse packet input := query (.encodeResponse packet input)

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
end BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad


/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.run_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.run_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.run_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.ext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program.ext
