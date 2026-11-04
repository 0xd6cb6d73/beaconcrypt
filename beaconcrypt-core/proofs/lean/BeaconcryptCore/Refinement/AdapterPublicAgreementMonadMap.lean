-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! A source Rust computation may be moved between effect monads by a lawful monad interpretation that preserves the actual enclosing Rust result. These are algebraic laws of the interpretation, separate from all source-controller and primitive functional guarantees. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap
open AdapterPublicWrapperRustT (RustT)
variable {left right : Type → Type} [Monad left] [Monad right]
class Transformation (left right : Type → Type) [Monad left] [Monad right] where
  transform : {A : Type} → RustT left A → RustT right A
  lawful : Cslib.IsMonadHom (RustT left) (RustT right) transform
  lift : ∀ {A : Type} (result : RustM A), transform (AdapterRecordRequestMonad.liftRust result) = AdapterRecordRequestMonad.liftRust result

variable [translation : Transformation left right] {A B : Type}
def mapped (work : RustT left A) : RustT right A := translation.transform work

theorem mapped_pure (value : A) : mapped (left := left) (right := right) (pure value) = pure value :=
  translation.lawful.map_pure value

theorem mapped_liftRust (result : RustM A) :
    mapped (left := left) (right := right) (AdapterRecordRequestMonad.liftRust result) = AdapterRecordRequestMonad.liftRust result :=
  translation.lift result

theorem mapped_bind (work : RustT left A) (next : A → RustT left B) :
    mapped (right := right) (work >>= next) = (mapped work >>= fun value => mapped (next value)) :=
  translation.lawful.map_bind work next
end BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap.mapped_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap.mapped_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap.mapped_liftRust' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap.mapped_liftRust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap.mapped_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap.mapped_bind
