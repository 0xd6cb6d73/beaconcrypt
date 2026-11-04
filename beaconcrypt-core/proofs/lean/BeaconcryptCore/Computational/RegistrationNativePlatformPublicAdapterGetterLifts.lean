-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
/-! Pure opaque-object getters retain their original functional contract through the actual uniform counter, World lens and platform interpretation. Source-local leaf lifting likewise preserves pure replies without access to native metadata. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {S P A : Type}

theorem lift_pure (value : A) :
    RegistrationNativePlatformPublicAdapterLeaves.lift (S:=S) (pure value : RustT (StateT P ProbComp) A)=pure value :=by
  apply RustT.ext
  apply StateT.ext
  intro before
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_pure,StateT.run_lift,pure_bind,StateT.run_pure]

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}

theorem ed_public (coins : QueryImpl unifSpec (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (contract : ∀key,original.edPublicBytes key=pure (view.edPublic key)) (key : ed.PublicKey) :
    (@CryptoOperations.edPublicBytes material ed
      (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run=pure (.ok (view.edPublic key)) :=by
  change (AdapterPublicAgreementOracleInterpretation.transform coins
    (AdapterPublicAgreementNativeWorldMap.transform
      (AdapterPublicAgreementCountedRust.counted (original.edPublicBytes key)))).run=_
  rw [contract,AdapterPublicAgreementCountedRust.counted_pure,AdapterPublicAgreementNativeWorldMap.transform_pure,
    AdapterPublicAgreementOracleInterpretation.transform_pure,RustT.run_pure]

variable [platform : PublicWrapperPlatform.Platform]
variable [originalLocal : LocalOperations (RustT (StateT P ProbComp))]

omit original in
theorem mldsa (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (contract : ∀identity,(originalLocal.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))
    (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) :
    ((RegistrationNativePlatformPublicAdapterLeaves.localOperations (S:=RegistrationNativeExperiment.State n KemSK mlSource)
      originalLocal).auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey) :=by
  change StateT.lift (originalLocal.auth_MldsaIdentity_public_key identity).run=_
  rw [contract]
  apply StateT.ext
  intro before
  simp only [StateT.run_lift,StateT.run_pure,pure_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts.lift_pure' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts.lift_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts.ed_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts.ed_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts.mldsa' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts.mldsa
