-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration
import BeaconcryptCore.Refinement.AdapterServerConstructorJoint
import BeaconcryptCore.Computational.RegistrationAgreementSampledState
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
/-! Server startup maps the same original optional Ed generation and mandatory ML generation through the literal uniform counter. Constructor refusal, private object realizations and returned RNG remain joint with the actual startup state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformPublicAdapterUniformObserver (observe lift_observe)
variable {n : Nat} {A : Type}

def uniform : QueryImpl unifSpec (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun query=>PqxdhRecordLiftWorld.sampled (unifSpec.query query)

theorem sampled (work : ProbComp A) :
    simulateQ (uniform (n:=n)) work=PqxdhRecordLiftWorld.sampled work := by
  induction work using OracleComp.inductionOn with
  | pure value=>
    apply StateT.ext
    intro before
    rw [simulateQ_pure,StateT.run_pure,RegistrationAgreementSampledState.sampled_pure]
  | query_bind query next ih=>
    rw [simulateQ_bind,simulateQ_spec_query]
    simp only [ih]
    apply StateT.ext
    intro before
    rw [StateT.run_bind,RegistrationAgreementSampledState.sampled_bind]
    rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable (kem : {R E : Type} → rand_core.TryCryptoRng R E → R → RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair ed.Error×R))
variable {R Error KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)

noncomputable def signing (joint : PqxdhJointIdentity.Primitives)
    (sample : ProbComp (Option PqxdhJointIdentity.IdentitySeed))
    (contract : AdapterServerConstructorJoint.EdContract generator view joint sample) :
    letI : AdapterBeaconConstructorRequestMonad.Operations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp)):=
      RegistrationNativePlatformPublicAdapterCreateGeneration.operations uniform original kem
    AdapterServerConstructorJoint.EdContract (m:=StateT (PqxdhRecordLiftWorld.State n) ProbComp) generator view joint (PqxdhRecordLiftWorld.sampled sample) := by
  letI : AdapterBeaconConstructorRequestMonad.Operations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp)):=
    RegistrationNativePlatformPublicAdapterCreateGeneration.operations uniform original kem
  refine {
    joint:=fun rng=>simulateQ uniform (contract.joint rng)
    nativeMarginal:=?_
    realize:=contract.realize
    privateView:=contract.privateView
    publicView:=contract.publicView
    failure:=contract.failure
    operation:=?_ }
  · intro rng
    rw [←simulateQ_map,contract.nativeMarginal,sampled]
  · intro rng
    change observe uniform (original.edGenerate generator rng)=_
    rw [contract.operation,lift_observe,simulateQ_map]

noncomputable def mldsa (sample : ProbComp (Option (RegistrationNativeMldsa.Credential mlSource)))
    (contract : AdapterServerConstructorGeneration.MldsaContract generator view sample) :
    letI : AdapterBeaconConstructorRequestMonad.Operations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp)):=
      RegistrationNativePlatformPublicAdapterCreateGeneration.operations uniform original kem
    AdapterServerConstructorGeneration.MldsaContract (m:=StateT (PqxdhRecordLiftWorld.State n) ProbComp) generator view (PqxdhRecordLiftWorld.sampled sample) := by
  rw [←sampled]
  exact RegistrationNativePlatformPublicAdapterCreateGeneration.mldsa uniform kem generator view sample contract

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration.sampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration.sampled
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration.signing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration.mldsa' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration.mldsa
