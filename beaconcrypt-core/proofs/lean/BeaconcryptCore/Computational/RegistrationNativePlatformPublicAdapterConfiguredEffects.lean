-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
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
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
variable (current :RegistrationNativeExperiment.State n KemSK source×P)
variable (before :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem coin_target (query :unifSpec.Domain) :
    (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.world (RegistrationNativePlatformPublicAdapterEffects.world (.inl query)))).run current.1).run current.2))=
      ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inl query)).run current) :=by
  change _=RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inl query)).run current.1).run current.2)
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native
  rw [RegistrationNativePlatformPublicAdapterRawModel.coin]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def coin (query :unifSpec.Domain) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential)
      (((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inl query)).run current)) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (coin_target configuration created credential current query)
    (RegistrationNativePlatformPublicAdapterEffects.step coins setup configuration.view configuration.views created credential current before (.inl query))

noncomputable def coinSource (query :unifSpec.Domain)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :=
  RegistrationNativePlatformPublicAdapterEffectPhysical.run setup checks configuration.agreement.representation created coins (.inl query) before

omit [PublicWrapperPlatform.CryptoOperations] in
theorem coin_query (query :unifSpec.Domain) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential)
      (coin configuration created credential current before query)=
      coinSource configuration created query
        (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential current before) :=by
  rw [coin,RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  exact RegistrationNativePlatformPublicAdapterEffectPhysical.normalized setup checks configuration.agreement.representation created coins
    configuration.view configuration.views credential current before (.inl query)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem hash_target (query :Pqxdh.Bytes) :
    (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.world (RegistrationNativePlatformPublicAdapterEffects.world (.inr query)))).run current.1).run current.2))=
      ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.hash query))).run current) :=by
  change _=RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.hash query))).run current.1).run current.2)
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native
  rw [RegistrationNativePlatformPublicAdapterRawModel.hash]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def hash (query :Pqxdh.Bytes) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential)
      (((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.hash query))).run current)) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (hash_target configuration created credential current query)
    (RegistrationNativePlatformPublicAdapterEffects.step coins setup configuration.view configuration.views created credential current before (.inr query))

noncomputable def hashSource (query :Pqxdh.Bytes)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :=
  RegistrationNativePlatformPublicAdapterEffectPhysical.run setup checks configuration.agreement.representation created coins (.inr query) before

omit [PublicWrapperPlatform.CryptoOperations] in
theorem hash_query (query :Pqxdh.Bytes) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential)
      (hash configuration created credential current before query)=
      hashSource configuration created query
        (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential current before) :=by
  rw [hash,RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  exact RegistrationNativePlatformPublicAdapterEffectPhysical.normalized setup checks configuration.agreement.representation created coins
    configuration.view configuration.views credential current before (.inr query)
omit [PublicWrapperPlatform.CryptoOperations] in
theorem hmac_target (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes) :
    pure (setup.hmac.eval key message,current)=
      ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.hmac key message))).run current) :=by
  change _=RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.hmac key message))).run current.1).run current.2)
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native
  rw [RegistrationNativePlatformPublicAdapterRawModel.hmac]
  simp only [StateT.run_pure,map_pure]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def hmac (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential)
      (((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.hmac key message))).run current)) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (hmac_target configuration created credential current key message)
    (RegistrationNativePlatformPublicAdapterEffectPhysical.pureStep setup configuration.view configuration.views created credential current before (setup.hmac.eval key message))

noncomputable def hmacSource (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    ProbComp (RustM (PqxdhSecretInputKdf.HmacBlock×RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)×
      (RegistrationNativePlatformSdkReification.Backend n KemSK×P)) :=
  pure (.ok (setup.hmac.eval key message,before),before.backend)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem hmac_query (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential)
      (hmac configuration created credential current before key message)=
      hmacSource (setup:=setup) key message
        (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential current before) :=by
  rw [hmac,RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  have same:=RegistrationNativePlatformPublicAdapterEffectPhysical.pure_source setup configuration.view configuration.views created credential current before (setup.hmac.eval key message)
  have basis:=before.base.backend
  change (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects).backend=
    RegistrationNativePlatformSdkReification.persistent current at basis
  unfold hmacSource
  rw [←basis] at same
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.coin_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.coin_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.coin_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.coin_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hash_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hash_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hash_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hash_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hmac_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hmac_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hmac_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects.hmac_query
