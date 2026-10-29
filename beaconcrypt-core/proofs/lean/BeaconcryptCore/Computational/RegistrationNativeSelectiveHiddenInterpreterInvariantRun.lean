-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantProgram

/-! The literal complete native run starts the thin service with its actual empty allocator. Its ordered injective address assignment and demand bill follow from the actual interpreter and original public CE budget, without an externally supplied invariant or whole-program demand cap. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSelectiveHiddenInterpreter (State initial)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreterInvariant (Good)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Outcome (Value : Type) (source : RegistrationNativeMldsa.Source) :=
  (Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source

/-- Every supported actual native run preserves the ordered injective literal-input allocator from its actual empty initialization. -/
theorem run_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source) (result : Outcome Value source × State n KemSK ProviderState)
    (supported : result ∈ support (RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept serverKeyId bounds mode work frontend (initial providerState))) : Good result.2 :=
  RegistrationNativeSelectiveHiddenInterpreterInvariantProgram.program_good setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider _ _ result (RegistrationNativeSelectiveHiddenInterpreterInvariant.initial_good providerState) supported

/-- The original build-plus-finish CE bill bounds the actual thin demand counter after every native success or failure outcome. -/
theorem run_count (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (frontend : RegistrationNativePublicFrontend.State source) (result : Outcome Value source × State n KemSK ProviderState)
    (supported : result ∈ support (RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept serverKeyId bounds mode work frontend (initial providerState))) :
    result.2.1.keys.demands ≤ budget.cap 4 + budget.cap 5 := by
  have actual := RegistrationNativeSelectiveHiddenInterpreterInvariantProgram.program_count setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider _ (budget.cap 4 + budget.cap 5)
    (RegistrationNativePublicCaps.run_bound setup checks wire source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work budget bounded frontend)
    (initial providerState) result (RegistrationNativeSelectiveHiddenInterpreterInvariant.initial_good providerState) supported
  simpa only [initial, RegistrationNativeHiddenInterpreter.initial, RegistrationNativeHiddenService.initial, Nat.zero_add] using actual

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantRun.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantRun.run_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantRun.run_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantRun.run_count
