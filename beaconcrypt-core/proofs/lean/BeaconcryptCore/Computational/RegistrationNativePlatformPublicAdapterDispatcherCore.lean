-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins

abbrev Private (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (current :RegistrationNativeExperiment.State n KemSK source×P) :=
  RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup configuration.view configuration.views created credential current

noncomputable def native (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source) :=
  RegistrationNativePlatformPublicAdapterRawModel.raw (n:=n) setup checks configuration.agreement.representation created credential
    configuration.keyView configuration.sealFailure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
    (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets)

noncomputable def model (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source) :
    QueryImpl RegistrationNativePlatformPublicAdapterInterface.Spec (StateT (Native×P) ProbComp)
  | .inl query=>fun current=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((native configuration created credential (.inl query)).run current.1).run current.2)
  | .inr query=>fun current=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((native configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand query))).run current.1).run current.2)

noncomputable def physical (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (current :RegistrationNativeExperiment.State n KemSK source×P) (before :Private configuration created credential current) :=
  RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)

-- The active drivers replace every used child field. These explicit short-circuiting fallbacks are unreachable by the proved literal source-body decompositions.
@[instance_reducible] noncomputable def children {m :Type→Type} [Monad m] :ChildOperations (RustT m) where
  executeHash _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  authenticateInit _ _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  authenticateResponse _ _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  commitmentHash _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  openRequest _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  ratchetHkdf _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  compare _ _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  encodeInit _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  encodeResponse _:=AdapterRecordRequestMonad.liftRust (.fail .panic)

noncomputable def other {m :Type→Type} [Monad m] :QueryImpl AdapterInitAuthenticationRequestMonad.Spec m:=
  fun _=>pure (.fail .panic)
noncomputable def recording {m :Type→Type} [Monad m] :QueryImpl AdapterRecordRequestMonad.Spec m:=
  fun _=>pure (.fail .panic)

noncomputable def packed (work :RustT (StateT P ProbComp) A) :RustT (StateT (S×P) ProbComp) A:=
  ⟨fun before=>(fun result=>(result.1,(before.1,result.2))) <$>work.run.run before.2⟩

@[instance_reducible] noncomputable def packedLocal :LocalOperations (RustT (StateT (S×P) ProbComp)) where
  auth_MldsaIdentity_public_key identity:=packed (originalLocal.auth_MldsaIdentity_public_key identity)
  auth_MldsaIdentity_sign_requested identity request:=packed (originalLocal.auth_MldsaIdentity_sign_requested identity request)
  ratchet_initial_ratchet_hkdf request:=packed (originalLocal.ratchet_initial_ratchet_hkdf request)
  collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher value:=packed (originalLocal.collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher value)
  ratchet_execute_seal_request request:=packed (originalLocal.ratchet_execute_seal_request request)
  ratchet_execute_write_request request:=packed (originalLocal.ratchet_execute_write_request request)

noncomputable def packedCoins :QueryImpl unifSpec (StateT (S×P) ProbComp):=fun query before=>
  (fun result=>(result.1,(before.1,result.2))) <$>(coins query).run before.2

@[instance_reducible] noncomputable def packedCrypto :CryptoOperations (RustT (StateT (S×P) ProbComp)):=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations packedCoins originalCrypto

omit originalGenerators originalCrypto originalLocal originalContainers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] primitives in
theorem raw_cast {N Reply :Type} {Private :N→Type} {left right :ProbComp (Reply×N)}
    (same :left=right) (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep Private left)
    (physical :∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical
      (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast same call)=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical call :=rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore.model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore.model

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore.physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast
