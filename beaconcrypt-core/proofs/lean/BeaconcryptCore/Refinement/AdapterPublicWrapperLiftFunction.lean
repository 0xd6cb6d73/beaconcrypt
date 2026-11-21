import BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction
open AdapterRecordRequestMonad (LiftRust liftRust)
universe u v w
class LiftFunction (m : Type → Type) (F : Type u) (G : outParam (Type v)) where
  lift : F → G

def call {m : Type → Type} {F : Type u} {G : Type v} [LiftFunction m F G] (source : F) : G :=
  LiftFunction.lift (m := m) source

instance result {m : Type → Type} [LiftRust m] {A : Type} :
    LiftFunction m (RustM A) (m A) := ⟨liftRust⟩
instance function {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] :
    LiftFunction m ((a : A) → F a) ((a : A) → G a) :=
  ⟨fun source arg => call (m := m) (source arg)⟩

instance fnonce {m : Type → Type} [LiftRust m] {F T U : Type} :
    LiftFunction m (core.ops.function.FnOnce F T U) (AdapterPublicWrapperRequestMonad.FnOnce m F T U) :=
  ⟨AdapterPublicWrapperRequestMonad.FnOnce.liftRust⟩

instance fnmut {m : Type → Type} [LiftRust m] {F T U : Type} :
    LiftFunction m (core.ops.function.FnMut F T U) (AdapterPublicWrapperRequestMonad.FnMut m F T U) :=
  ⟨AdapterPublicWrapperRequestMonad.FnMut.liftRust⟩

instance fn {m : Type → Type} [LiftRust m] {F T U : Type} :
    LiftFunction m (core.ops.function.Fn F T U) (AdapterPublicWrapperRequestMonad.Fn m F T U) :=
  ⟨AdapterPublicWrapperRequestMonad.Fn.liftRust⟩

variable {A B : Type}
theorem result_rust (source : RustM A) : call (m := RustM) source = source := rfl
theorem function_rust (source : A → RustM B) : call (m := RustM) source = source := rfl
theorem dependent_rust {C : A → Type} (source : (a : A) → RustM (C a)) :
    call (m := RustM) source = source := rfl

def loopFuel {m : Type → Type} [Monad m] [LiftRust m] {Input Output : Type} :
    Nat → (Input → m (ControlFlow Input Output)) → Input → m Output
  | 0, _, _ => liftRust .div
  | fuel + 1, body, before => do
      match ← body before with
      | .cont after => loopFuel fuel body after
      | .done value => pure value
end BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.result_rust' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.result_rust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.function_rust' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.function_rust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.dependent_rust' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.dependent_rust
