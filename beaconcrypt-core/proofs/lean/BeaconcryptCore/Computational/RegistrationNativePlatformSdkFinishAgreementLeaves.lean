-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame
import BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementLeaves
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 CipherArray Keys)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformSdkFinishSampling (sample uniform)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

 theorem query (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup originalModel.decapsulate)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view keys owner oneTime)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem)
    (request : RegistrationAgreementExecutor.Request) (allowed : RegistrationAgreementBeaconCoverage.Allowed request) :
    letI : CryptoOperations (RustT (StateT (Backend n KemSK) ProbComp)) :=
      RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created)
        (RegistrationNativeAgreementJournal.core setup owner oneTime request)).run before =
      (AdapterPublicAgreementCapture.implementation
        (RegistrationNativePlatformPublicAdapterCommonModel.model (uniform (n:=n) (KemSK:=KemSK)) setup view originalModel) keys request).run (erase before) := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) ProbComp)) :=
    RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
  cases request with
  | generate role | encapsulate input => exact False.elim allowed
  | decapsulate input =>
      cases input with
      | none =>
          simp only [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
            RegistrationNativeKemInterface.beacon,simulateQ_pure,StateT.run_pure,map_pure,
            AdapterPublicAgreementCapture.implementation,AdapterPublicAgreementCommonModel.decapsulate]
          rfl
      | some input =>
          simp only [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
            RegistrationNativeKemInterface.beacon,simulateQ_map,simulateQ_spec_query,StateT.run_map,
            Functor.map_map,AdapterPublicAgreementCapture.implementation,AdapterPublicAgreementCommonModel.decapsulate,
            related.kemStored,RegistrationNativePlatformPublicAdapterCommonModel.model]
          have leaf:=RegistrationNativePlatformSdkFinishDecapsulation.source_leaf setup checks representation created
            originalModel.decapsulate aligned before canonical owner.kemHandle pair present input
          rw [sameSecret] at leaf
          exact leaf
  | convertPublic key =>
      simp [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
        RegistrationNativeKemInterface.beacon,RegistrationNativeKemInterface.other,
        RegistrationNativeKemBackend.beaconOther,RegistrationNativeKemInterface.OtherRequest.primitive,
        RegistrationBeaconRoleBackend.native,RegistrationBeaconRoleBackend.localBackend,
        RegistrationNativeAgreementJournal.coins,AdapterPublicAgreementCapture.implementation,
        StateT.run,StateT.monad_pure_def,StateT.pure]
  | convertSecret role =>
      change role=.LocalIdentity at allowed
      subst role
      simp [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
        RegistrationNativeKemInterface.beacon,RegistrationNativeKemInterface.other,
        RegistrationNativeKemBackend.beaconOther,RegistrationNativeKemInterface.OtherRequest.primitive,
        RegistrationBeaconRoleBackend.native,RegistrationBeaconRoleBackend.localBackend,
        RegistrationNativeAgreementJournal.coins,AdapterPublicAgreementCapture.implementation,
        StateT.run,RegistrationServerRoleBackend.selected_conversion setup originalModel.representation]
      change Prod.map id erase <$> (pure (_,before) : ProbComp _) = pure (_,erase before)
      rw [map_pure]
      rfl
  | dh request =>
      rcases request with ⟨role,publicKey⟩
      cases role with
      | LocalIdentity =>
          simp [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
            RegistrationNativeKemInterface.beacon,RegistrationNativeKemInterface.other,
            RegistrationNativeKemBackend.beaconOther,RegistrationNativeKemInterface.OtherRequest.primitive,
            RegistrationBeaconRoleBackend.native,RegistrationBeaconRoleBackend.localBackend,
            RegistrationNativeAgreementJournal.coins,AdapterPublicAgreementCapture.implementation,
            AdapterPublicAgreementCommonModel.dh,AdapterPublicAgreementPrimitiveModel.selected,
            AdapterPublicAgreementCapture.capture,related.identity,AdapterPublicAgreementNativeDh.identity_native,StateT.run]
          change Prod.map id erase <$> (pure (_,before) : ProbComp _) = pure (_,erase before)
          rw [map_pure]
          rfl
      | ServerEphemeral =>
          simp [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
            RegistrationNativeKemInterface.beacon,RegistrationNativeKemInterface.other,
            RegistrationNativeKemBackend.beaconOther,RegistrationNativeKemInterface.OtherRequest.primitive,
            RegistrationBeaconRoleBackend.native,RegistrationBeaconRoleBackend.localBackend,
            RegistrationNativeAgreementJournal.coins,AdapterPublicAgreementCapture.implementation,
            AdapterPublicAgreementCommonModel.dh,AdapterPublicAgreementPrimitiveModel.selected,
            AdapterPublicAgreementCapture.capture,StateT.run]
          change Prod.map id erase <$> (pure (_,before) : ProbComp _) = pure (_,erase before)
          rw [map_pure]
          rfl
      | BeaconPrekey =>
          simp [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
            RegistrationNativeKemInterface.beacon,RegistrationNativeKemInterface.other,
            RegistrationNativeKemBackend.beaconOther,RegistrationNativeKemInterface.OtherRequest.primitive,
            RegistrationBeaconRoleBackend.native,RegistrationBeaconRoleBackend.localBackend,
            RegistrationNativeAgreementJournal.coins,AdapterPublicAgreementCapture.implementation,
            AdapterPublicAgreementCommonModel.dh,AdapterPublicAgreementPrimitiveModel.selected,
            related.prekeyStored,related.prekeyView,AdapterPublicAgreementNativeDh.scalar_native,StateT.run]
          change Prod.map id erase <$> (pure (_,before) : ProbComp _) = pure (_,erase before)
          rw [map_pure]
          rfl
      | BeaconOneTime =>
          simp [RegistrationNativeAgreementJournal.core,RegistrationNativeAgreementJournal.primitive,
            RegistrationNativeKemInterface.beacon,RegistrationNativeKemInterface.other,
            RegistrationNativeKemBackend.beaconOther,RegistrationNativeKemInterface.OtherRequest.primitive,
            RegistrationBeaconRoleBackend.native,RegistrationBeaconRoleBackend.localBackend,
            RegistrationNativeAgreementJournal.coins,AdapterPublicAgreementCapture.implementation,
            AdapterPublicAgreementCommonModel.dh,AdapterPublicAgreementPrimitiveModel.selected,
            related.oneTimeStored,related.oneTimeView,AdapterPublicAgreementNativeDh.scalar_native,StateT.run]
          change Prod.map id erase <$> (pure (_,before) : ProbComp _) = pure (_,erase before)
          rw [map_pure]
          rfl
  | root request =>
      simp only [RegistrationNativeAgreementJournal.core,simulateQ_pure,StateT.run_pure,map_pure,
        AdapterPublicAgreementCapture.implementation]
      rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementLeaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementLeaves.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementLeaves.query
