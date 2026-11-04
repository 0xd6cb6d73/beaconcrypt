-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterSealExtraction.Funs
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad
import BeaconcryptCore.AdapterSealJoinRequestExtraction

/-! The seal dispatcher separates the public allocator request from the native AEAD request. Key/nonce conversion and standard wrappers retain their exact RustM results. Rust failure, divergence and ordinary optional rejection remain distinct; this interface assumes no primitive or source-security law. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterSealRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
variable [primitives : AdapterSealPrimitive.Operations]

class Operations (E : Type) (m : Type → Type) where
  reserve : alloc.vec.Vec U8 → Usize → m (core.result.Result Unit E × alloc.vec.Vec U8)
  aead : Slice U8 → core.option.Option (Slice U8) → primitives.Nonce → primitives.Key →
    m (core.result.Result (alloc.vec.Vec U8 × alloc.vec.Vec U8) primitives.Error)

namespace Lifted
variable {m : Type → Type} [LiftRust m]

def key (value : Array U8 32#usize) := liftRust (core.convert.Into.Blanket.into
  beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832 value) (m := m)
def nonce (value : Array U8 12#usize) := liftRust (core.convert.Into.Blanket.into
  beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812 value) (m := m)
def arraySlice {N : Usize} (value : Array U8 N) := liftRust (core.array.Array.as_slice value) (m := m)
def resultOk {A Error : Type} (value : core.result.Result A Error) := liftRust (core.result.Result.ok value) (m := m)
def branch {A : Type} (value : core.option.Option A) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch value) (m := m)
def fromResidual (value : core.option.Option core.convert.Infallible) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (alloc.vec.Vec U8 × Array U8 16#usize) value) (m := m)
def slice (value : alloc.vec.Vec U8) := liftRust (alloc.vec.Vec.as_slice value) (m := m)
def tag (value : Slice U8) := liftRust
  (core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
    16#usize core.U8.Insts.CoreMarkerCopy value) (m := m)
def protect (value : alloc.vec.Vec U8) := liftRust (zeroize.Zeroizing.new
  (zeroize.alloc.vec.Vec.Insts.ZeroizeZeroize
    (zeroize.Zeroize.Blanket zeroize.U8.Insts.ZeroizeDefaultIsZeroes)) value) (m := m)
def optionRef {A : Type} (value : core.option.Option A) := liftRust (core.option.Option.as_ref value) (m := m)
def deref (value : zeroize.Zeroizing (alloc.vec.Vec U8)) := liftRust
  (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
    (zeroize.alloc.vec.Vec.Insts.ZeroizeZeroize
      (zeroize.Zeroize.Blanket zeroize.U8.Insts.ZeroizeDefaultIsZeroes)) value) (m := m)

def join {E : Type} [Monad m] [operations : Operations E m] (parts : Array (Slice U8) 2#usize) :
    m (core.option.Option (alloc.vec.Vec U8)) :=
  let _ : AdapterSealJoinRequestMonad.Operations E m := ⟨operations.reserve⟩
  AdapterSealJoinRequestExtraction.join (E := E) parts
end Lifted

inductive Request where
  | reserve (before : alloc.vec.Vec U8) (capacity : Usize)
  | aead (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
      (nonce : primitives.Nonce) (key : primitives.Key)

abbrev Response (E : Type) : Request → Type
  | .reserve _ _ => core.result.Result Unit E × alloc.vec.Vec U8
  | .aead _ _ _ _ => core.result.Result (alloc.vec.Vec U8 × alloc.vec.Vec U8) primitives.Error
abbrev Spec (E : Type) : OracleSpec Request := fun request => RustM (Response E request)

structure Program (E : Type) (A : Type) where
  run : OracleComp (Spec E) (RustM A)

namespace Program
variable {E A B : Type}
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
  aead plaintext associated nonce key := query (.aead plaintext associated nonce key)

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
end BeaconcryptCore.Refinement.AdapterSealRequestMonad

/-- info: 'BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.run_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealRequestMonad.Program.ext
