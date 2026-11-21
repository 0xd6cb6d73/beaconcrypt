-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemStartup
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame

/-! The complete original-ledger open native G2 client has one ordinary selected-owner KEM hop. Its genuine on-demand source, private uniform108 table, actual startup failures and complete/no-getter branches remain inside the explicitly constructed adversary. Public budgets derive all private capacity and no-reveal obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSecurity
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- One actual parsed-accept/owner target incurs coefficient-one KEM CCA and correctness losses, with its original full native ledger and any decision retained literally. -/
theorem native_close (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (selected : Fin (budget.create + 1)) :
    let work := RegistrationNativeOpenKeyStartup.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selected.val selectedAccept bounds mode adversary decision
    (RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem work).boolDistance
      (RegistrationNativeOpenKeyKemGame.uniform setup.baseImpl setup.kem work budget.create selected 0) ≤
      (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (RegistrationNativeOpenKeyKemGame.adversary setup.baseImpl setup.kem work budget.create selected 0).toINDCCA).toReal +
      RegistrationNativeKemTotalCorrectness.correctnessError setup.baseImpl setup.kem := by
  dsimp only
  exact RegistrationNativeOpenKeyKemGame.normal_close setup.baseImpl setup.kem functional _ budget.create selected 0
    (RegistrationNativeOpenKeyKemStartup.creates setup checks wire route source ensureInit identityIndex serverKeyId
      selected.val selectedAccept bounds mode adversary decision budget bounded)
    (RegistrationNativeOpenKeyKemStartup.no_reveal setup checks wire route source ensureInit identityIndex serverKeyId
      selected.val selectedAccept bounds mode adversary decision budget bounded)

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSecurity.native_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSecurity.native_close
