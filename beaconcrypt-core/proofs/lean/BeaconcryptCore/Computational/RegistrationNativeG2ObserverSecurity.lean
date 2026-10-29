-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame

/-! The actual chronological G2 observer has a coefficient-one selected-key KEM hop with its original query bills. Its decision may inspect the real prepare/demand/encapsulation/install trace. This bounds the real-to-candidate transition of that concrete observer; it does not assert a later adaptive alias bound or a complete APP entropy theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG2ObserverSecurity
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
    (observe : PqxdhJointIdentity.IdentitySeed → PqxdhJointGapDh.ScalarBytes → RegistrationNativeG2Observer.Outcome Value → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (selected : Fin (budget.create + 1)) :
    let work := RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selected.val selectedAccept bounds mode adversary observe
    (RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem work).boolDistance
      (RegistrationNativeOpenKeyKemGame.uniform setup.baseImpl setup.kem work budget.create selected 0) ≤
      (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (RegistrationNativeOpenKeyKemGame.adversary setup.baseImpl setup.kem work budget.create selected 0).toINDCCA).toReal +
      RegistrationNativeKemTotalCorrectness.correctnessError setup.baseImpl setup.kem := by
  dsimp only
  exact RegistrationNativeOpenKeyKemGame.normal_close setup.baseImpl setup.kem functional _ budget.create selected 0
    (RegistrationNativeG2ObserverCaps.creates setup checks wire route source ensureInit identityIndex serverKeyId
      selected.val selectedAccept bounds mode adversary observe budget bounded)
    (RegistrationNativeG2ObserverCaps.no_reveal setup checks wire route source ensureInit identityIndex serverKeyId
      selected.val selectedAccept bounds mode adversary observe budget bounded)

end BeaconcryptCore.Computational.RegistrationNativeG2ObserverSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2ObserverSecurity.native_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2ObserverSecurity.native_close
