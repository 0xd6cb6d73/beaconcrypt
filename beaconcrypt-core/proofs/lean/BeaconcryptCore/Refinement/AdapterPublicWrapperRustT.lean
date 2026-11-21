-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad

/-! The effectful public wrapper runs Rust results above the shared native/platform monad. Failure and divergence stop the source continuation while preserving every already reached native and platform poststate. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperRustT

structure RustT (m : Type → Type) (A : Type) where
  run : m (RustM A)

namespace RustT
variable {m : Type → Type} {A B C : Type}

theorem ext (left right : RustT m A) (same : left.run = right.run) : left = right := by
  cases left
  cases right
  cases same
  rfl

variable [Monad m]
def pure (value : A) : RustT m A := ⟨Pure.pure (.ok value)⟩
def bind (work : RustT m A) (next : A → RustT m B) : RustT m B := ⟨do
  let result ← work.run
  match result with
  | .ok value => (next value).run
  | .fail error => Pure.pure (.fail error)
  | .div => Pure.pure .div⟩

instance : Monad (RustT m) where
  pure := pure
  bind := bind

instance : AdapterRecordRequestMonad.LiftRust (RustT m) where
  liftRust result := ⟨Pure.pure result⟩

def lift (work : m A) : RustT m A := ⟨RustM.ok <$> work⟩

@[simp] theorem run_pure (value : A) : (Pure.pure value : RustT m A).run = Pure.pure (.ok value) := rfl
@[simp] theorem run_liftRust (result : RustM A) :
    (AdapterRecordRequestMonad.liftRust result : RustT m A).run = Pure.pure result := rfl
@[simp] theorem run_bind (work : RustT m A) (next : A → RustT m B) :
    (work >>= next).run = (do
      let result ← work.run
      match result with
      | .ok value => (next value).run
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) := rfl
@[simp] theorem run_lift (work : m A) : (lift work).run = RustM.ok <$> work := rfl

variable [LawfulMonad m]
instance : LawfulMonad (RustT m) := LawfulMonad.mk' (RustT m)
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
        | .div => Pure.pure .div) = (Pure.pure : RustM A → m (RustM A)) := by
      funext result
      cases result <;> rfl
    rw [same, bind_pure])
  (by
    intros
    apply ext
    simp only [run_bind, run_pure, pure_bind])
  (by
    intros
    apply ext
    simp only [run_bind, bind_assoc]
    refine bind_congr fun result => ?_
    cases result <;> simp only [pure_bind])

theorem lift_bind (work : m A) (next : A → m B) :
    lift (work >>= next) = (lift work >>= fun value => lift (next value)) := by
  apply ext
  simp only [run_lift, run_bind, bind_map_left, map_bind]

theorem lift_pure (value : A) : lift (Pure.pure value : m A) = Pure.pure value := by
  apply ext
  simp only [run_lift, map_pure, run_pure]

end RustT

variable {m : Type → Type} [Monad m] {State A B : Type}
theorem shared_bind (work : RustT (StateT State m) A) (next : A → RustT (StateT State m) B) (before : State) :
    ((work >>= next).run).run before = (do
      let result ← work.run.run before
      match result.1 with
      | .ok value => (next value).run.run result.2
      | .fail error => pure (.fail error, result.2)
      | .div => pure (.div, result.2)) := by
  simp only [RustT.run_bind, StateT.run_bind]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

end BeaconcryptCore.Refinement.AdapterPublicWrapperRustT

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.ext' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.ext

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_liftRust' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_liftRust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_lift' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.lift_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.lift_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.lift_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT.lift_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.shared_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.shared_bind
