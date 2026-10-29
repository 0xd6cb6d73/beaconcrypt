-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginalProgram
import BeaconcryptCore.Computational.RegistrationNativeStartupMetricSource
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal

/-! The old original ledger decision is exactly the pure candidate-independent marginal of the unchanged whole startup/value client. Actual startup source and bilateral compiler accounting laws establish this equation before normal KEM closure. The later ordinary observed CCA hop can therefore act once on the full-value client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (observe : Value × RegistrationNativeLedger.State → Bool)

/-- The original executable client decision is exactly the final ledger marginal of the unchanged complete startup/value client. -/
theorem client_source :
    RegistrationNativeOpenKeyStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary observe =
      RegistrationNativeG3NativeStartupDecision.decision observe <$>
        RegistrationNativeG3NativeStartupUniformValue.program (n := n) setup checks wire source route ensureInit identityIndex serverKeyId
          selectedOwner selectedAccept bounds mode adversary := by
  rw [RegistrationNativeG3NativeStartupMarginalProgram.reference_source, RegistrationNativeG3NativeStartupMarginalProgram.actual_source]
  unfold RegistrationNativeG3NativeStartupMarginalProgram.reference RegistrationNativeG3NativeStartupMarginalProgram.actual
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  rw [RegistrationNativeStartupMetric.cold_source]

/-- Normal KEM closure preserves the exact original candidate-independent ledger decision marginal. -/
theorem normal_source :
    RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyStartup.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary observe) =
      RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
        (simulateQ RegistrationNativeOpenKey.native
          (RegistrationNativeG3NativeStartupDecision.decision observe <$>
            RegistrationNativeG3NativeStartupUniformValue.program (n := n) setup checks wire source route ensureInit identityIndex serverKeyId
              selectedOwner selectedAccept bounds mode adversary)) := by
  rw [RegistrationNativeOpenKeyStartup.nativeClient, client_source]

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource.client_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource.normal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupNormalSource.normal_source
