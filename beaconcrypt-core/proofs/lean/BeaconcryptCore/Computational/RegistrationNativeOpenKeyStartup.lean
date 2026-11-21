-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedStartup
import BeaconcryptCore.Computational.RegistrationNativeOpenKey

/-! The complete open key/KEM client samples its independent Server/prekey challenges locally before the literal counted native startup. Its only unavailable KEM capability is the external indexed pool/selected encapsulation service. Reassociation yields the precise native cut interface, with the108-byte table in a pool-free ambient branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def coins : QueryImpl unifSpec (OracleComp (RegistrationNativeOpenKey.Spec KemSK)) :=
  RegistrationNativeOpenKey.keyLift ∘ₛ RegistrationNativeKeyCompiler.coins

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) : OracleComp (RegistrationNativeOpenKey.Spec KemSK) Bool := do
  let seed ← simulateQ coins PqxdhJointIdentity.sampleSeed
  let scalar ← simulateQ coins PqxdhJointGapDh.sampleScalar
  RegistrationNativeOpenKey.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (RegistrationNativeOpenRetainedStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary decision (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))

noncomputable def nativeClient (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) : OracleComp (RegistrationNativeOpenKey.NativeSpec KemSK) Bool :=
  simulateQ RegistrationNativeOpenKey.native
    (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision)

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup
