-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
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
local notation "TypedSpec"=>RegistrationNativeRawAdapter.TypedSpec
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

noncomputable def typed (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source) :
    QueryImpl TypedSpec (StateT (Native×P) ProbComp) :=fun query=>
  RegistrationNativePlatformPackedState.pack
    (RegistrationNativePlatformPublicAdapterRawModel.typed (n:=n) setup checks configuration.agreement.representation created credential
      configuration.keyView configuration.sealFailure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
      configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
      (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
      (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) query)

def failure (credential :RegistrationNativeMldsa.Credential source) (query :RegistrationNativeRawAdapter.TypedSpec.Domain)
    (reply :RegistrationNativeRawAdapter.TypedSpec.Range query) (before :RegistrationNativeExperiment.State n KemSK source×P) :Prop :=
  RegistrationNativeMldsaOriginEvent.Bad source credential query before.1 reply

abbrev State (n :Nat) (KemSK P :Type) (source :RegistrationNativeMldsa.Source) :=
  (RegistrationNativeExperiment.State n KemSK source×P)×
    RegistrationNativePlatformPublicAdapterTypedAudit.Audit RegistrationNativeRawAdapter.TypedSpec
      (RegistrationNativeExperiment.State n KemSK source×P)

noncomputable def raw (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source) :
    QueryImpl RegistrationNativeInterface.Spec (StateT (State n KemSK P source) ProbComp) :=
  RegistrationNativeRawAdapter.handler RegistrationNativeConcreteCodec.wire
    (RegistrationNativePlatformPublicAdapterTypedAudit.handler (typed configuration created credential) (failure credential))

noncomputable def model (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source) :
    QueryImpl RegistrationNativePlatformPublicAdapterInterface.Spec (StateT (State n KemSK P source) ProbComp)
  | .inl query=>raw configuration created credential (.inl query)
  | .inr query=>raw configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand query))

abbrev Private (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (before :State n KemSK P source) :=
  RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential before.1

noncomputable def physical (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (before :State n KemSK P source) (stored :Private configuration created credential before) :=
  RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential before.1 stored

omit [PublicWrapperPlatform.CryptoOperations] in
theorem raw_native (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (query :RegistrationNativeInterface.Spec.Domain) (before :State n KemSK P source) :
    Prod.map id Prod.fst <$> ((raw configuration created credential query).run before)=
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential query)).run before.1 :=by
  unfold raw RegistrationNativeRawAdapter.handler
  rw [QueryImpl.apply_compose,RegistrationNativePlatformPublicAdapterTypedAudit.native_program]
  have same:=RegistrationNativePlatformPackedState.simulate_pack
    (RegistrationNativePlatformPublicAdapterRawModel.typed (n:=n) setup checks configuration.agreement.representation created credential
      configuration.keyView configuration.sealFailure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
      configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
      (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
      (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets))
    (RegistrationNativeRawAdapter.adapter RegistrationNativeConcreteCodec.wire query)
  exact congrArg (fun implementation=>implementation.run before.1) same.symm

omit [PublicWrapperPlatform.CryptoOperations] in
theorem native_query (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (query :RegistrationNativePlatformPublicAdapterInterface.Spec.Domain) (before :State n KemSK P source) :
    Prod.map id Prod.fst <$> ((model configuration created credential query).run before)=
      ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential query).run before.1) :=by
  cases query with
  | inl coin=>exact raw_native configuration created credential (.inl coin) before
  | inr command=>exact raw_native configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command)) before

omit [PublicWrapperPlatform.CryptoOperations] in
theorem native_program {Value :Type} (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (work :OracleComp RegistrationNativePlatformPublicAdapterInterface.Spec Value) (before :State n KemSK P source) :
    Prod.map id Prod.fst <$> (simulateQ (model configuration created credential) work).run before=
      (simulateQ (RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (native_query configuration created credential) work before

omit [PublicWrapperPlatform.CryptoOperations] in
theorem raw_program {Value :Type} (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (work :OracleComp RegistrationNativePlatformPublicAdapterInterface.Spec Value) :
    simulateQ (model (n:=n) configuration created credential) work=
      simulateQ (raw (n:=n) configuration created credential)
        (simulateQ RegistrationNativePlatformPublicAdapterInterface.adapter work) :=by
  rw [←QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation=>simulateQ implementation work)
  funext query
  cases query with
  | inl coin=>simp only [QueryImpl.apply_compose,RegistrationNativePlatformPublicAdapterInterface.adapter,simulateQ_spec_query];rfl
  | inr command=>simp only [QueryImpl.apply_compose,RegistrationNativePlatformPublicAdapterInterface.adapter,simulateQ_spec_query];rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.raw_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.raw_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.native_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.native_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.native_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel.raw_program
