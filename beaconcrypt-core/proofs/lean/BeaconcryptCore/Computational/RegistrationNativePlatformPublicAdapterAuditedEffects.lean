-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects
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
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
variable (current :RegistrationNativeExperiment.State n KemSK source×P)
variable (prior :RegistrationNativePlatformPublicAdapterTypedAudit.Audit RegistrationNativeRawAdapter.TypedSpec
  (RegistrationNativeExperiment.State n KemSK source×P))
variable (before :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current)

omit primitives originalGenerators originalCrypto originalLocal originalContainers
  [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] in
private theorem raw_id {N Reply :Type} {Private :N→Type} {target :ProbComp (Reply×N)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep Private target)
    (physical :∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical (RegistrationNativePlatformPublicAdapterReply.map id call)=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical call :=rfl

omit [PublicWrapperPlatform.CryptoOperations] in
theorem coin_target (query :unifSpec.Domain) :
    ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inl query)).run current)=
      ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inl query)).run current) :=rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def coinTyped (query :unifSpec.Domain) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (coin_target configuration created credential current query)
    (RegistrationNativePlatformPublicAdapterConfiguredEffects.coin configuration created credential current before query)

noncomputable def coin (query :unifSpec.Domain) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential (.inl query) (.inl query) id rfl
    current prior (coinTyped configuration created credential current before query)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem coin_query (query :unifSpec.Domain) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential)
      (coin configuration created credential current prior before query)=
      RegistrationNativePlatformPublicAdapterConfiguredEffects.coinSource configuration created query
        (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential current before) :=by
  unfold coin
  rw [RegistrationNativePlatformPublicAdapterAuditLift.selected_physical,raw_id]
  unfold coinTyped
  rw [RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  exact RegistrationNativePlatformPublicAdapterConfiguredEffects.coin_query configuration created credential current before query

omit [PublicWrapperPlatform.CryptoOperations] in
theorem hash_target (query :Pqxdh.Bytes) :
    ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.hash query))).run current)=
      ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.hash query))).run current) :=by
  change (RegistrationNativePlatformPackedState.pack
    (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.hash query)))).run current=_
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native RegistrationNativePlatformPublicAdapterRawModel.raw
  simp only [QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def hashTyped (query :Pqxdh.Bytes) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (hash_target configuration created credential current query)
    (RegistrationNativePlatformPublicAdapterConfiguredEffects.hash configuration created credential current before query)

noncomputable def hash (query :Pqxdh.Bytes) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential (.inr (.hash query)) (.inr (.hash query)) id rfl
    current prior (hashTyped configuration created credential current before query)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem hash_query (query :Pqxdh.Bytes) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential)
      (hash configuration created credential current prior before query)=
      RegistrationNativePlatformPublicAdapterConfiguredEffects.hashSource configuration created query
        (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential current before) :=by
  unfold hash
  rw [RegistrationNativePlatformPublicAdapterAuditLift.selected_physical,raw_id]
  unfold hashTyped
  rw [RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  exact RegistrationNativePlatformPublicAdapterConfiguredEffects.hash_query configuration created credential current before query

omit [PublicWrapperPlatform.CryptoOperations] in
theorem hmac_target (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes) :
    ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.hmac key message))).run current)=
      ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.hmac key message))).run current) :=rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def hmacTyped (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (hmac_target configuration created credential current key message)
    (RegistrationNativePlatformPublicAdapterConfiguredEffects.hmac configuration created credential current before key message)

noncomputable def hmac (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential (.inr (.hmac key message)) (.inr (.hmac key message)) id rfl
    current prior (hmacTyped configuration created credential current before key message)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem hmac_query (key :PqxdhSecretInputKdf.HmacBlock) (message :Pqxdh.Bytes) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential)
      (hmac configuration created credential current prior before key message)=
      RegistrationNativePlatformPublicAdapterConfiguredEffects.hmacSource (setup:=setup) key message
        (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential current before) :=by
  unfold hmac
  rw [RegistrationNativePlatformPublicAdapterAuditLift.selected_physical,raw_id]
  unfold hmacTyped
  rw [RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  exact RegistrationNativePlatformPublicAdapterConfiguredEffects.hmac_query configuration created credential current before key message

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.coin_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.coin_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.coin_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.coin_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hash_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hash_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hash_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hash_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hmac_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hmac_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hmac_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects.hmac_query
