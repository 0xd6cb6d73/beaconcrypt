-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals
import BeaconcryptCore.Computational.RegistrationNativeEvents

/-! A selected final installation ordinal is expressed only using the original claim, fresh ledger, public transcript and complete native trace. A same-execution hidden-origin invariant then attaches the actual claimed physical handle without identifying private intermediate cuts from marginal source laws. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallTarget
variable {Value : Type} {n : Nat}

def Claimed (claim : Value → Option (Nat × Pqxdh.Bytes)) (value : Value)
    (ledger : RegistrationNativeLedger.State) (events : List RegistrationNativeG2Trace.Event)
    (selected : RegistrationNativeRelatedFamily.Message → Prop) : Prop :=
  ∃ index guess entry role ordinal message,
    claim value = some (index, guess) ∧ ledger.ledger.fresh[index]? = some entry ∧ entry.message = guess ∧
    RegistrationNativeInstallOrdinals.At role events ledger.transcript ordinal message entry.handle ∧ selected message

/-- A selected final ordinal and the actual same-execution hidden-origin invariant give the claimed physical hidden handle. -/
theorem hidden (claim : Value → Option (Nat × Pqxdh.Bytes)) (value : Value)
    (ledger : RegistrationNativeLedger.State) (events : List RegistrationNativeG2Trace.Event)
    (selected : RegistrationNativeRelatedFamily.Message → Prop)
    (slots : PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (claimed : Claimed claim value ledger events selected)
    (origins : RegistrationNativeInstallOrdinals.Hidden events ledger.transcript slots selected) :
    ∃ index guess entry, claim value = some (index, guess) ∧ ledger.ledger.fresh[index]? = some entry ∧
      entry.message = guess ∧ (slots entry.handle).isSome := by
  obtain ⟨index, guess, entry, role, ordinal, message, claimAt, fresh, guessed, paired, chosen⟩ := claimed
  exact ⟨index, guess, entry, claimAt, fresh, guessed, origins role ordinal message entry.handle paired chosen⟩

end BeaconcryptCore.Computational.RegistrationNativeInstallTarget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTarget.hidden' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTarget.hidden
