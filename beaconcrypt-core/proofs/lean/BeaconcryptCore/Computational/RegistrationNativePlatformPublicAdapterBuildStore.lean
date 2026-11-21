-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification
/-! The Builder's physical Server row is reified from the actual returned source Server/map and actual raw-attempt count. It never copies a final model World or receives a continuation/backend law from the caller. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStore
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend persistent backend worldBackend)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {KemSK P :Type} {mlSource :RegistrationNativeMldsa.Source}

def committed (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (views :AdapterPublicWrapperStorage.Views)
    (returned :beaconcrypt_public_wrapper.server.Server) (raw :Backend n KemSK×P) :Backend n KemSK×P :=
  let attempts:=(raw.1.world.server.map (fun records=>records.records.rawAttempts)).getD 0
  let records:=AdapterPublicOrdinaryServerReifier.server view views returned attempts
  (⟨raw.1.auxiliary,raw.1.pool,worldBackend {raw.1.world with server:=some records}⟩,raw.2)

theorem snapshot_source (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (views :AdapterPublicWrapperStorage.Views)
    (returned :beaconcrypt_public_wrapper.server.Server) (raw :RegistrationNativeExperiment.State n KemSK mlSource×P) :
    persistent (RegistrationNativePlatformSdkServerReification.snapshot view views returned none raw).committed=
      committed view views returned (persistent raw) := by
  simp only [RegistrationNativePlatformSdkServerReification.snapshot,RegistrationNativePlatformSdkServerReification.rawAttempts,
    RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot.committed,committed,persistent,backend,worldBackend,
    Function.update_idem]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStore.snapshot_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStore.snapshot_source
