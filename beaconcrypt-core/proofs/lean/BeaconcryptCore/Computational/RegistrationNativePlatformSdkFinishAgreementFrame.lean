-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementLeaves
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementFrame
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformSdkFinishSampling (sample uniform)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem pure_frame (value : A) (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (result : A × Backend n KemSK) (supported : result∈support (pure (value,before) :ProbComp _)) :
    result.2.pool=before.pool ∧result.2.auxiliary=before.auxiliary ∧worldBackend result.2.world=result.2.world := by
  simp only [support_pure,Set.mem_singleton_iff] at supported
  cases supported
  exact ⟨rfl,rfl,canonical⟩

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]

 theorem source_frame (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (keys : Keys) (request : RegistrationAgreementExecutor.Request)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (result : RegistrationAgreementExecutor.Spec.Range request × Backend n KemSK) :
    letI : CryptoOperations (RustT (StateT (Backend n KemSK) ProbComp)) :=
      RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
    result∈support ((AdapterPublicAgreementCapture.implementation
      (RegistrationNativePlatformPublicAdapterCommonModel.model (uniform (n:=n) (KemSK:=KemSK)) setup view originalModel) keys request).run before) →
    result.2.pool=before.pool ∧result.2.auxiliary=before.auxiliary ∧worldBackend result.2.world=result.2.world := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) ProbComp)) :=
    RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
  intro supported
  cases request with
  | decapsulate input =>
      cases input with
      | none =>exact pure_frame _ before canonical result supported
      | some input =>
          cases stored:keys.beacon_kem with
          | none =>
              simp only [AdapterPublicAgreementCapture.implementation,AdapterPublicAgreementCommonModel.decapsulate,stored] at supported
              exact pure_frame _ before canonical result supported
          | some secret =>
              simp only [AdapterPublicAgreementCapture.implementation,AdapterPublicAgreementCommonModel.decapsulate,stored,
                RegistrationNativePlatformPublicAdapterCommonModel.model] at supported
              rw [RegistrationNativePlatformSdkFinishSampling.program] at supported
              exact RegistrationNativePlatformSdkFinishSampleFrame.frame _ before canonical result supported
  | _=>exact pure_frame _ before canonical result supported

 theorem native_frame (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup originalModel.decapsulate)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view keys owner oneTime)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem)
    (request : RegistrationAgreementExecutor.Request) (allowed : RegistrationAgreementBeaconCoverage.Allowed request)
    (result : RegistrationAgreementExecutor.Spec.Range request × Backend n KemSK)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created)
      (RegistrationNativeAgreementJournal.core setup owner oneTime request)).run before)) :
    result.2.pool.keys=before.pool.keys ∧worldBackend result.2.world=result.2.world := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) ProbComp)) :=
    RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
  have projected : (result.1,erase result.2)∈support ((AdapterPublicAgreementCapture.implementation
      (RegistrationNativePlatformPublicAdapterCommonModel.model (uniform (n:=n) (KemSK:=KemSK)) setup view originalModel) keys request).run (erase before)) := by
    rw [←RegistrationNativePlatformSdkFinishAgreementLeaves.query setup checks representation created view originalModel aligned
      keys owner oneTime related before canonical pair present sameSecret request allowed,support_map]
    exact ⟨result,supported,rfl⟩
  have frame:=source_frame setup view originalModel keys request (erase before) canonical (result.1,erase result.2) projected
  have keys : (erase result.2).pool.keys=(erase before).pool.keys :=
    congrArg (fun pool : PqxdhLiveKemBirth.Pool KemSK => pool.keys) frame.1
  exact ⟨keys,frame.2.2⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementFrame.source_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementFrame.source_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementFrame.native_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementFrame.native_frame
