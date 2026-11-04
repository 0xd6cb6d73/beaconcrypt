-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
/-! The isolated outer-send source fixture only distributes consumption of a read-only optional detached view over its two constructors. The monadic law retains every view/consumer result and poststate; the concrete law uses the actual Vec view and pending core resume. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Refinement.AdapterRecordSendBorrow
variable {A B C : Type} {m : Type → Type} [Monad m]
def optional (view : A → m B) (input : core.option.Option A) : m (core.option.Option B) :=
  match input with
  | .None => pure .None
  | .Some value => do
      let result ← view value
      pure (.Some result)

/-- Optional borrowed-view consumption distributes without adding or reordering an effect. -/
theorem consume_optional [LawfulMonad m] (view : A → m B) (consume : core.option.Option B → m C)
    (input : core.option.Option A) :
    (do let selected ← optional view input; consume selected) =
      (match input with
       | .None => consume .None
       | .Some value => do let selected ← view value; consume (.Some selected)) := by
  cases input <;> simp only [optional, pure_bind, bind_assoc]
def detachedView : core.ops.function.FnOnce Unit
    (alloc.vec.Vec U8 × Array U8 16#usize) (Slice U8 × Array U8 16#usize) where
  call_once _ value := do
    let bytes ← alloc.vec.Vec.as_slice value.1
    pure (bytes, value.2)

omit [Monad m] in
/-- The concrete original map/consume and localized resume have exactly the same enclosing Rust outcome and whole pending kernel. -/
theorem aead_resume (pending : beaconcrypt_core.record_effects.SealAead)
    (detached : core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize)) :
    (show RustM beaconcrypt_core.record_effects.SealAfterAead from do
      let borrowed : core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize) ← core.option.Option.as_ref detached
      let selected ← core.option.Option.map detachedView borrowed ()
      pending.resume selected) =
    (show RustM beaconcrypt_core.record_effects.SealAfterAead from do
      let borrowed : core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize) ← core.option.Option.as_ref detached
      match borrowed with
      | .None => pending.resume .None
      | .Some (body, tag) => do
          let bytes ← alloc.vec.Vec.as_slice body
          pending.resume (.Some (bytes, tag))) := by
  cases detached with
  | none => rfl
  | some pair =>
      rcases pair with ⟨body, tag⟩
      rfl

end BeaconcryptCore.Refinement.AdapterRecordSendBorrow

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordSendBorrow.consume_optional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordSendBorrow.consume_optional

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordSendBorrow.aead_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordSendBorrow.aead_resume
