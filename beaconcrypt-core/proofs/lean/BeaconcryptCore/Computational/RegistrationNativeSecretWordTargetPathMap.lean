-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! Concrete per-step source diagrams transport actual chronological original-ledger cuts. Literal query and reply entries remain unchanged while the same complete source states are mapped pointwise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathMap
open RegistrationNativeInterface (FullSpec Entry)
open RegistrationNativeSecretWordTargetPath (Path)
variable {First Second : Type}

/-- Mapping each actual supported call maps every same-run prefix, selected call and continuation without replacing the original transcript. -/
theorem map (source : QueryImpl FullSpec (StateT First ProbComp)) (target : QueryImpl FullSpec (StateT Second ProbComp))
    (state : First → Second)
    (step : ∀ query before result, result ∈ support ((source query).run before) →
      (result.1, state result.2) ∈ support ((target query).run (state before)))
    {before after : First} {entries : List Entry} (path : Path source before entries after) :
    Path target (state before) entries (state after) := by
  induction path with
  | nil before => exact .nil _
  | cons query reply before middle after tail called later ih =>
      exact .cons query reply (state before) (state middle) (state after) tail (step query before (reply, middle) called) ih
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathMap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathMap.map' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathMap.map
