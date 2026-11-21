-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
/-! The same actual counted primitive computation runs through the same persistent platform before and after backend erasure. The key-generation specialization retains its actual private pair, caller RNG and every Rust outcome. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n : Nat} {KemSK Platform A : Type} {source : RegistrationNativeMldsa.Source}

theorem transform_platform (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (work : RustT ProbComp A) (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (((AdapterPublicAgreementOracleInterpretation.transform coins
        (RegistrationNativePlatformSdkCountedReification.native work)).run.run before).run previous)=
      (((AdapterPublicAgreementOracleInterpretation.transform coins
        (RegistrationNativePlatformPublicAdapterCrypto.transform work)).run.run (backend before)).run previous) := by
  change Prod.map (Prod.map id backend) id <$>
    (simulateQ coins ((RegistrationNativePlatformSdkCountedReification.native work).run.run before)).run previous=
    (simulateQ coins ((RegistrationNativePlatformPublicAdapterCrypto.transform work).run.run (backend before))).run previous
  rw [←RegistrationNativePlatformPublicAdapterCrypto.transform_backend work before,simulateQ_map,StateT.run_map]
  rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]

@[instance_reducible] noncomputable def operations (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (original : CryptoOperations (RustT ProbComp)) :
    CryptoOperations (RustT (StateT (Backend n KemSK) (StateT Platform ProbComp))) :=
  AdapterPublicAgreementOracleInterpretation.operations coins (RegistrationNativePlatformPublicAdapterCrypto.operations original)

theorem generation {R Error : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      ((((AdapterPublicAgreementNativePlatformInterpreter.operations coins original).kxGenerate generator rng).run.run before).run previous)=
      ((((operations coins original).kxGenerate generator rng).run.run (backend before)).run previous) :=
  transform_platform coins (original.kxGenerate generator rng) before previous

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform.transform_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform.transform_platform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform.generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform.generation
