-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementProgram
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformSdkFinishSampling (uniform)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

noncomputable def closed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (Backend n KemSK) ProbComp) :=
  RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created ∘ₛ
    RegistrationNativeAgreementJournal.core setup owner oneTime

 theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup originalModel.decapsulate)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view keys owner oneTime)
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (bounded : RegistrationAgreementBeaconCoverage.Bound work)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem) :
    letI : CryptoOperations (RustT (StateT (Backend n KemSK) ProbComp)) :=
      RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
    Prod.map id erase <$>
      (simulateQ (closed setup checks representation created owner oneTime) work).run before =
      (simulateQ (AdapterPublicAgreementCapture.implementation
        (RegistrationNativePlatformPublicAdapterCommonModel.model (uniform (n:=n) (KemSK:=KemSK)) setup view originalModel) keys) work).run (erase before) := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) ProbComp)) :=
    RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure];rfl
  | query_bind request next ih =>
      rw [RegistrationAgreementBeaconCoverage.Bound,isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
      have leaf:=RegistrationNativePlatformSdkFinishAgreementLeaves.query setup checks representation created view originalModel aligned
        keys owner oneTime related before canonical pair present sameSecret request bounded.1
      change Prod.map id erase <$> (closed setup checks representation created owner oneTime request).run before = _ at leaf
      rw [←leaf,bind_map_left]
      apply OracleComp.bind_congr_of_forall_mem_support
      rintro ⟨reply,after⟩ reached
      have kept:=RegistrationNativePlatformSdkFinishAgreementFrame.native_frame setup checks representation created view originalModel aligned
        keys owner oneTime related before canonical pair present sameSecret request bounded.1 (reply,after) reached
      apply ih reply (bounded.2 reply) after kept.2
      rw [kept.1]
      exact present

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementProgram.program
