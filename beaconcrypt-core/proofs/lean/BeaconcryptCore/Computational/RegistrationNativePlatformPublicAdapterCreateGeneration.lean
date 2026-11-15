-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver
import BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
/-! Original probabilistic primitive contracts supply shared Server ML generation and Beacon Ed/X25519 methods after explicit uniform observation. Actual Beacon creation uses only Ed, X25519 and KEM. The joint private object and caller RNG are preserved. KEM remains a separate source operation because its actual private-pair birth also updates the source pool. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformPublicAdapterUniformObserver (observe lift_observe)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable (uniform : QueryImpl unifSpec m)

@[instance_reducible] def operations
    (original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp))
    (kem : {R E : Type} → rand_core.TryCryptoRng R E → R → RustT m
      (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair ed.Error × R)) :
    AdapterBeaconConstructorRequestMonad.Operations (RustT m) where
  mldsaGenerate generator rng := observe uniform (original.mldsaGenerate generator rng)
  edGenerate generator rng := observe uniform (original.edGenerate generator rng)
  kemGenerate := kem

variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable (kem : {R E : Type} → rand_core.TryCryptoRng R E → R → RustT m
  (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair ed.Error × R))

noncomputable def mldsa {R Error KemSK : Type} {source : RegistrationNativeMldsa.Source}
    (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (sample : ProbComp (Option (RegistrationNativeMldsa.Credential source)))
    (contract : AdapterServerConstructorGeneration.MldsaContract generator view sample) :
    let : AdapterBeaconConstructorRequestMonad.Operations (RustT m) := operations uniform original kem
    AdapterServerConstructorGeneration.MldsaContract generator view (simulateQ uniform sample) := by
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT m) := operations uniform original kem
  refine { joint := fun rng => simulateQ uniform (contract.joint rng), nativeMarginal := ?_, realize := contract.realize, privateView := contract.privateView, operation := ?_ }
  · intro rng
    rw [← simulateQ_map, contract.nativeMarginal]
  · intro rng
    change observe uniform (original.mldsaGenerate generator rng) = _
    rw [contract.operation, lift_observe, simulateQ_map]

noncomputable def signing {R Error KemSK : Type} {source : RegistrationNativeMldsa.Source}
    (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (sample : ProbComp PqxdhJointIdentity.IdentitySeed)
    (contract : AdapterBeaconConstructorGeneration.EdContract generator view joint sample) :
    let : AdapterBeaconConstructorRequestMonad.Operations (RustT m) := operations uniform original kem
    AdapterBeaconConstructorGeneration.EdContract generator view joint (simulateQ uniform sample) := by
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT m) := operations uniform original kem
  refine { joint := fun rng => simulateQ uniform (contract.joint rng), nativeMarginal := ?_, realize := contract.realize, privateView := contract.privateView, publicView := contract.publicView, operation := ?_ }
  · intro rng
    rw [← simulateQ_map, contract.nativeMarginal]
  · intro rng
    change observe uniform (original.edGenerate generator rng) = _
    rw [contract.operation, lift_observe, simulateQ_map]

omit original kem in
noncomputable def prekey [crypto : CryptoOperations (RustT ProbComp)]
    {R Error KemSK : Type} {source : RegistrationNativeMldsa.Source}
    (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (publicKey : PqxdhJointGapDh.ScalarBytes → Std.Array U8 32#usize)
    (sample : ProbComp PqxdhJointGapDh.ScalarBytes)
    (contract : AdapterBeaconConstructorGeneration.KxContract generator view publicKey sample) :
    let : CryptoOperations (RustT m) := RegistrationNativePlatformPublicAdapterUniformObserver.operations uniform crypto
    AdapterBeaconConstructorGeneration.KxContract generator view publicKey (simulateQ uniform sample) := by
  let : CryptoOperations (RustT m) := RegistrationNativePlatformPublicAdapterUniformObserver.operations uniform crypto
  refine { joint := fun rng => simulateQ uniform (contract.joint rng), nativeMarginal := ?_, realize := contract.realize, privateView := contract.privateView, publicView := contract.publicView, operation := ?_ }
  · intro rng
    rw [← simulateQ_map, contract.nativeMarginal]
  · intro rng
    change observe uniform (crypto.kxGenerate generator rng) = _
    rw [contract.operation, lift_observe, simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration.mldsa' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration.mldsa
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration.signing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration.prekey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration.prekey
