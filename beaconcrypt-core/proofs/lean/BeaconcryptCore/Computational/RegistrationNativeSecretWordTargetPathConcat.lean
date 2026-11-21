-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! Chronological source paths concatenate at their literal common cut state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
open RegistrationNativeSecretWordTargetPath (Path)
variable {NativeState : Type}

/-- Joining actual supported prefixes at the same intermediate state retains every original callback. -/
theorem append (implementation : QueryImpl RegistrationNativeInterface.FullSpec (StateT NativeState ProbComp))
    {before middle after : NativeState} {first last : List RegistrationNativeInterface.Entry}
    (prior : Path implementation before first middle) (later : Path implementation middle last after) :
    Path implementation before (first ++ last) after := by
  induction prior with
  | nil before => exact later
  | cons query reply before reached middle tail called remaining ih =>
      exact .cons query reply before reached after (tail ++ last) called (ih later)
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat.append' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat.append
