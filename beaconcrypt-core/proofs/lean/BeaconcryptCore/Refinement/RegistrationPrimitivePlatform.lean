import Aeneas
import CoreModels

set_option warningAsError true

/-!
The pinned core-model interface omits standard arithmetic names used by
the generated CBOR code. These definitions lift the existing Aeneas unsigned
shift and division semantics, including division-by-zero failure. They contain
no parser operation or additional functional assumption.
-/

def core.num.U8.wrapping_shl (value : Aeneas.Std.U8) (amount : Aeneas.Std.U32) :
    Aeneas.Std.RustM Aeneas.Std.U8 :=
  .ok (Aeneas.Std.core.num.U8.wrapping_shl value amount)

def core.num.U8.wrapping_shr (value : Aeneas.Std.U8) (amount : Aeneas.Std.U32) :
    Aeneas.Std.RustM Aeneas.Std.U8 :=
  .ok (Aeneas.Std.core.num.U8.wrapping_shr value amount)

def core.num.Usize.wrapping_div (left right : Aeneas.Std.Usize) :
    Aeneas.Std.RustM Aeneas.Std.Usize :=
  Aeneas.Std.UScalar.div left right

def core.num.U16.wrapping_div (left right : Aeneas.Std.U16) :
    Aeneas.Std.RustM Aeneas.Std.U16 :=
  Aeneas.Std.UScalar.div left right

def core.num.U32.wrapping_div (left right : Aeneas.Std.U32) :
    Aeneas.Std.RustM Aeneas.Std.U32 :=
  Aeneas.Std.UScalar.div left right

def core.num.U64.wrapping_div (left right : Aeneas.Std.U64) :
    Aeneas.Std.RustM Aeneas.Std.U64 :=
  Aeneas.Std.UScalar.div left right

namespace BeaconcryptCore.Refinement.RegistrationPrimitivePlatform

theorem wrapping_shl_eq (value : Aeneas.Std.U8) (amount : Aeneas.Std.U32) :
    core.num.U8.wrapping_shl value amount =
      .ok (Aeneas.Std.core.num.U8.wrapping_shl value amount) := rfl

theorem wrapping_shr_eq (value : Aeneas.Std.U8) (amount : Aeneas.Std.U32) :
    core.num.U8.wrapping_shr value amount =
      .ok (Aeneas.Std.core.num.U8.wrapping_shr value amount) := rfl

theorem wrapping_div_eq (left right : Aeneas.Std.Usize) :
    core.num.Usize.wrapping_div left right = Aeneas.Std.UScalar.div left right := rfl

theorem wrapping_div_widths :
    (∀ left right : Aeneas.Std.U16,
      core.num.U16.wrapping_div left right = Aeneas.Std.UScalar.div left right) ∧
    (∀ left right : Aeneas.Std.U32,
      core.num.U32.wrapping_div left right = Aeneas.Std.UScalar.div left right) ∧
    (∀ left right : Aeneas.Std.U64,
      core.num.U64.wrapping_div left right = Aeneas.Std.UScalar.div left right) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitivePlatform.wrapping_shl_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms wrapping_shl_eq
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitivePlatform.wrapping_shr_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapping_shr_eq
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitivePlatform.wrapping_div_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapping_div_eq
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitivePlatform.wrapping_div_widths' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapping_div_widths

end BeaconcryptCore.Refinement.RegistrationPrimitivePlatform
