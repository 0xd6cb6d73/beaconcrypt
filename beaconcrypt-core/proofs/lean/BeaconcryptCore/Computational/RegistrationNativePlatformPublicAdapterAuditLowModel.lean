-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel
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
abbrev State (n :Nat) (KemSK P :Type) (source :RegistrationNativeMldsa.Source):=
  RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source

noncomputable def model (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source) :
    QueryImpl RegistrationNativePlatformPublicAdapterLowSpec.Spec (StateT (State n KemSK P source) ProbComp) :=
  RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential ∘ₛ
    RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter

noncomputable def coreModel (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source) :
    QueryImpl RegistrationNativePlatformPublicAdapterLowSpec.Spec (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp) :=
  (fun query=>RegistrationNativePlatformPackedState.pack (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential query)) ∘ₛ
    RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter

abbrev Private (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (before :State n KemSK P source):=
  RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential before

noncomputable def physical (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (before :State n KemSK P source) (stored :Private configuration created credential before):=
  RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential before stored

omit [PublicWrapperPlatform.CryptoOperations] in
theorem native_query (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :State n KemSK P source) :
    Prod.map id Prod.fst <$> ((model configuration created credential query).run before)=
      ((coreModel configuration created credential query).run before.1) :=by
  unfold model coreModel
  rw [QueryImpl.apply_compose,QueryImpl.apply_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (RegistrationNativePlatformPublicAdapterAuditModel.raw_native configuration created credential)
    (RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter query) before

omit [PublicWrapperPlatform.CryptoOperations] in
theorem native_program {Value :Type} (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value) (before :State n KemSK P source) :
    Prod.map id Prod.fst <$> (simulateQ (model configuration created credential) work).run before=
      (simulateQ (coreModel configuration created credential) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (native_query configuration created credential) work before

omit [PublicWrapperPlatform.CryptoOperations] in
theorem raw_program {Value :Type} (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value) :
    simulateQ (model (n:=n) configuration created credential) work=
      simulateQ (RegistrationNativePlatformPublicAdapterAuditModel.raw (n:=n) configuration created credential)
        (simulateQ RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter work) :=by
  unfold model
  exact QueryImpl.simulateQ_compose _ _ work

omit [PublicWrapperPlatform.CryptoOperations] in
theorem public_query (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (query :RegistrationNativePlatformPublicAdapterInterface.Spec.Domain) :
    model (n:=n) configuration created credential (.inl query)=
      RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential query :=by
  unfold model
  rw [QueryImpl.apply_compose]
  cases query with
  | inl coin=>simp only [RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter,RegistrationNativePlatformPublicAdapterInterface.adapter,simulateQ_spec_query];rfl
  | inr command=>simp only [RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter,RegistrationNativePlatformPublicAdapterInterface.adapter,simulateQ_spec_query];rfl

omit [PublicWrapperPlatform.CryptoOperations] in
theorem server_query (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (key :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    model (n:=n) configuration created credential (.inr (.serverSend key bytes oversized))=
      RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential (.inr (.serverSend key bytes)) :=by
  unfold model
  rw [QueryImpl.apply_compose,RegistrationNativePlatformPublicAdapterLowSpec.server_native,simulateQ_spec_query]

omit [PublicWrapperPlatform.CryptoOperations] in
theorem beacon_query (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (owner :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    model (n:=n) configuration created credential (.inr (.beaconSend owner bytes oversized))=
      RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential (.inr (.beaconSend owner bytes)) :=by
  unfold model
  rw [QueryImpl.apply_compose,RegistrationNativePlatformPublicAdapterLowSpec.beacon_native,simulateQ_spec_query]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.native_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.native_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.native_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.raw_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.public_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.public_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.server_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.server_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.beacon_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel.beacon_query
