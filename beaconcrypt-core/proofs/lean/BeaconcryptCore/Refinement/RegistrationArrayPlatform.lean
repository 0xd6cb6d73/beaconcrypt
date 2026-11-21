-- SPDX-License-Identifier: 0BSD
import Aeneas

set_option autoImplicit false
set_option warningAsError true

/-! The omitted standard unsigned remainder name uses the existing Aeneas
semantics, including zero-divisor panic. No codec or rotation law is assumed. -/

def core.num.Usize.wrapping_rem (left right : Aeneas.Std.Usize) :
    Aeneas.Std.RustM Aeneas.Std.Usize :=
  Aeneas.Std.UScalar.rem left right

namespace BeaconcryptCore.Refinement.RegistrationArrayPlatform

theorem wrapping_rem_eq (left right : Aeneas.Std.Usize) :
    core.num.Usize.wrapping_rem left right = Aeneas.Std.UScalar.rem left right := rfl

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayPlatform.wrapping_rem_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapping_rem_eq

end BeaconcryptCore.Refinement.RegistrationArrayPlatform
