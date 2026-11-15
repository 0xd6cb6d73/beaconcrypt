-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterInitAuthenticationExtraction.Funs
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad

/-! The actual source Init authentication loop requests the transcript hash together with its two separate Ed25519 leaves: public-key parsing and opening the attached signature. Every optional failure and primitive poststate remains in the interpretation; the std borrowed view retains the actual opened buffer. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad
variable [primitive : AdapterInitEdPrimitive.Operations]
open AdapterRecordRequestMonad (LiftRust liftRust)

class Operations (m : Type → Type) where
  hash : beaconcrypt_core.registration.HashRequest → m (core.option.Option (Array U8 64#usize))
  parseEd : Slice U8 → m (core.result.Result primitive.PublicKey primitive.Error)
  verifyEd : Slice U8 → primitive.PublicKey → m (core.option.Option (alloc.vec.Vec U8))

instance [beaconcrypt.auth.Operations] : Operations RustM where
  hash := beaconcrypt.auth.execute_hash
  parseEd := beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
  verifyEd := beaconcrypt_crypto.crypto_sign.verify

namespace Lifted
variable {m : Type → Type} [LiftRust m]

def hashRequest (pending : beaconcrypt_core.registration.InitHash) :=
  liftRust (beaconcrypt_core.registration.InitHash.request pending) (m := m)
def hashResume (pending : beaconcrypt_core.registration.InitHash) (reply : core.option.Option (Array U8 64#usize)) :=
  liftRust (beaconcrypt_core.registration.InitHash.resume pending reply) (m := m)
def edRequest (pending : beaconcrypt_core.registration.InitEd25519Verification) :=
  liftRust (beaconcrypt_core.registration.InitEd25519Verification.request pending) (m := m)
def edResume (pending : beaconcrypt_core.registration.InitEd25519Verification) (reply : core.option.Option (Slice U8)) :=
  liftRust (beaconcrypt_core.registration.InitEd25519Verification.resume pending reply) (m := m)

def resultOk (result : core.result.Result primitive.PublicKey primitive.Error) :=
  liftRust (core.result.Result.ok result) (m := m)
def branch (value : core.option.Option primitive.PublicKey) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch value) (m := m)
def fromResidual (residual : core.option.Option core.convert.Infallible) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (alloc.vec.Vec U8) residual) (m := m)
def toSlice (bytes : Array U8 32#usize) := liftRust (lift (Array.to_slice bytes)) (m := m)
def asDeref (opened : core.option.Option (alloc.vec.Vec U8)) :=
  liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) opened) (m := m)
end Lifted

inductive Request where
  | hash (request : beaconcrypt_core.registration.HashRequest)
  | parseEd (input : Slice U8)
  | verifyEd (signed : Slice U8) (publicKey : primitive.PublicKey)

abbrev Response : Request → Type
  | .hash _ => core.option.Option (Array U8 64#usize)
  | .parseEd _ => core.result.Result primitive.PublicKey primitive.Error
  | .verifyEd _ _ => core.option.Option (alloc.vec.Vec U8)

abbrev Spec : OracleSpec Request := fun request => RustM (Response request)

structure Program (A : Type) where
  run : OracleComp Spec (RustM A)

namespace Program
variable {A B C : Type}

def pure (value : A) : Program A := ⟨Pure.pure (.ok value)⟩
def bind (work : Program A) (next : A → Program B) : Program B := ⟨do
  let result ← work.run
  match result with
  | .ok value => (next value).run
  | .fail error => Pure.pure (.fail error)
  | .div => Pure.pure .div⟩

instance : Monad (Program) where
  pure := pure
  bind := bind

instance : LiftRust (Program) where
  liftRust value := ⟨Pure.pure value⟩

def query (request : Request) : Program (Response request) :=
  ⟨OracleComp.lift (Spec.query request)⟩

instance : Operations Program where
  hash request := query (.hash request)
  parseEd input := query (.parseEd input)
  verifyEd signed publicKey := query (.verifyEd signed publicKey)

@[simp] theorem run_pure (value : A) :
    (Pure.pure value : Program A).run = Pure.pure (.ok value) := rfl
@[simp] theorem run_lift (value : RustM A) :
    (liftRust value : Program A).run = Pure.pure value := rfl
@[simp] theorem run_bind (work : Program A) (next : A → Program B) :
    (work >>= next).run = (do
      let result ← work.run
      match result with
      | .ok value => (next value).run
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) := rfl

theorem ext (left right : Program A) (same : left.run = right.run) : left = right := by
  cases left
  cases right
  cases same
  rfl

instance : LawfulMonad (Program) := LawfulMonad.mk' (Program)
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
        | .div => Pure.pure .div) = (Pure.pure : RustM A → OracleComp Spec (RustM A)) := by
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
end BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.run_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationRequestMonad.Program.ext
