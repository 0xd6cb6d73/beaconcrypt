-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRun
import BeaconcryptCore.Computational.RegistrationNativeHiddenStartup

/-! The actual optional native startup either produces no continuation or initializes the exact thin allocator before the complete original ledger. Every supported successful branch inherits the original build-plus-finish demand bill and ordered injective literal-input allocation internally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (State Provider)
open RegistrationNativeHiddenInterpreterInvariant (Good)
open RegistrationNativeHiddenInterpreterInvariantRun (Outcome run_good run_count)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Result (n : Nat) (KemSK ProviderState Value : Type) (source : RegistrationNativeMldsa.Source) :=
  Option (PqxdhLiveServerConstruction.Created Unit × (Outcome Value source × State n KemSK ProviderState))

def Valid (budget : PqxdhDeploymentInterface.Budget) : Result n KemSK ProviderState Value source → Prop
  | none => True
  | some (_, result) => Good result.2 ∧ result.2.keys.demands ≤ budget.cap 4 + budget.cap 5

/-- Actual optional startup and the complete original native ledger derive their own allocator validity and finite demand bill on every supported outcome. -/
theorem program_valid (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (result : Result n KemSK ProviderState Value source)
    (supported : result ∈ support (RegistrationNativeHiddenStartup.program setup checks wire source ensureInit identityIndex serverKeyId
      seed scalar provider providerState selectedOwner selectedAccept bounds mode adversary)) : Valid budget result := by
  unfold RegistrationNativeHiddenStartup.program at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨initialized, _started, continued⟩ := supported
  cases initialized with
  | none =>
      rw [mem_support_pure_iff] at continued
      cases continued
      trivial
  | some born =>
      simp only [bind_pure_comp, support_map] at continued
      obtain ⟨observed, actual, returned⟩ := continued
      cases returned
      exact ⟨run_good setup checks wire born.native.credential seed scalar provider providerState selectedOwner selectedAccept
        serverKeyId bounds mode _ born.native.frontend observed actual,
        run_count setup checks wire born.native.credential seed scalar provider providerState selectedOwner selectedAccept
          serverKeyId bounds mode _ budget (bounded _) born.native.frontend observed actual⟩

end BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunStartup.program_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunStartup.program_valid
