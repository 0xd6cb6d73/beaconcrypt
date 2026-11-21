-- SPDX-License-Identifier: 0BSD
set_option autoImplicit false
set_option warningAsError true
/-! Whole-recursion computation at a known constructor preserves the dependent branch proof. These generic Sort-polymorphic equalities let SDK case dispatch be analyzed without rewriting actual source operands through their getter or material proof types. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases
universe u
theorem rec_none {T : Type} {U : Sort u} (value : Option T) (empty : value=none→U) (some : ∀word,value=Option.some word→U)
    (selected : value=none) :
    Option.rec (motive:=fun current=>value=current→U) empty some value rfl=empty selected := by
  cases selected
  rfl

theorem rec_some {T : Type} {U : Sort u} (value : Option T) (empty : value=none→U) (some : ∀word,value=Option.some word→U)
    (word : T) (selected : value=Option.some word) :
    Option.rec (motive:=fun current=>value=current→U) empty some value rfl=some word selected := by
  cases selected
  rfl

theorem rec_apply {T : Type} {U : Sort u} (left right : T) (operation : left=right→U) (same : left=right) :
    (Eq.rec (motive:=fun value _=>left=value→U) operation same.symm) rfl=operation same := by
  cases same
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases.rec_none' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases.rec_none

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases.rec_some' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases.rec_some

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases.rec_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases.rec_apply
