-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation
import BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! Every configured actual callback outside Bundle and Build preserves the exact signing-receipt prefix. Constructor failures and generation, incoming authentication/agreement, ordinary record callbacks and refused frame publication are all included. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame
attribute [local irreducible] RegistrationNativePlatformSourceAccept.accept
attribute [local irreducible] RegistrationNativeBeaconFrontend.create
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
variable {Value :Type}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
attribute [local irreducible] RegistrationNativeExperiment.handler

def Quiet :RegistrationNativeRawAdapter.TypedSpec.Domain→Prop
  | .inr (.bundle _) | .inr (.build _ _)=>False
  | _=>True

omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] originalGenerators originalCrypto in
private theorem after_cut (reserve :Nat→StateT P ProbComp (core.result.Result Unit E))
    (work :RegistrationNativePlatformOrdinaryExperiment.M n KemSK source P (Option RawCtxSourceSend.Encrypted))
    (before :Native) (previous :P) (result :(Option RawCtxSourceSend.Encrypted×Native)×P)
    (supported :result∈support (((RegistrationNativePlatformOrdinaryExperimentRouting.after reserve work).run before).run previous)) :
    ∃middle∈support ((work.run before).run previous),result.1.2=middle.1.2 :=by
  simp only [RegistrationNativePlatformOrdinaryExperimentRouting.after,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩:=supported
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at continued
  obtain ⟨gated,_reserved,same⟩:=continued
  exact ⟨middle,called,(congrArg (fun result=>result.1.2) same).symm⟩

omit [PublicWrapperPlatform.CryptoOperations] in
theorem handler (query :RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed :Quiet query)
    (before :Native) (previous :P) (result :(RegistrationNativeRawAdapter.TypedSpec.Range query×Native)×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterRawModel.typed setup checks configuration.agreement.representation created credential
      configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
      configuration.erased helper writer query).run before).run previous)) :
    result.1.2.server.world.world.2=before.server.world.world.2 :=by
  unfold RegistrationNativePlatformPublicAdapterRawModel.typed at supported
  rw [RegistrationNativePlatformExtractedExperiment.handler_source setup checks wire route configuration.agreement.representation created source credential
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    helper writer configuration.sealLength configuration.openLength configuration.converted configuration.edFunctional,
    RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at supported
  have prior (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain) (quiet :Quiet chosen)
      (returned :(RegistrationNativeRawAdapter.TypedSpec.Range chosen×Native)×P)
      (called :returned∈support (((RegistrationNativePlatformExperiment.handler coins setup checks canonical route configuration.agreement.representation created source credential
        configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.erased helper writer chosen).run before).run previous)) :
      returned.1.2.server.world.world.2=before.server.world.world.2 :=by
    cases chosen with
    | inl coin=>
      exact RegistrationNativePlatformReceiptPreservation.source_handler coins setup checks canonical route configuration.agreement.representation created credential
        configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.erased helper writer (.inl coin) (by trivial) before previous returned called
    | inr command=>cases command with
      | bundle _ | build _ _=>exact quiet.elim
      | create edPin mlPin keyId=>
        have original:=RegistrationNativePlatformHashReceipt.native_support coins _ returned.1 previous returned.2 called
        unfold RegistrationNativeExperiment.handler at original
        exact RegistrationNativeMldsaReceiptPreservation.beacon setup checks configuration.agreement.representation created _
          (RegistrationNativeMldsaNoSign.create setup edPin mlPin keyId) before returned.1 original
      | _=>
        exact RegistrationNativePlatformReceiptPreservation.source_handler coins setup checks canonical route configuration.agreement.representation created credential
          configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.erased helper writer _ (by trivial) before previous returned called
  have gated (work :RegistrationNativePlatformOrdinaryExperiment.M n KemSK source P (Option RawCtxSourceSend.Encrypted))
      (keeps :∀middle,middle∈support ((work.run before).run previous)→middle.1.2.server.world.world.2=before.server.world.world.2)
      (returned :(Option RawCtxSourceSend.Encrypted×Native)×P)
      (called :returned∈support (((RegistrationNativePlatformOrdinaryExperimentRouting.after configuration.reserveFrame work).run before).run previous)) :
      returned.1.2.server.world.world.2=before.server.world.world.2 :=by
    obtain ⟨middle,reached,same⟩:=after_cut configuration.reserveFrame work before previous returned called
    rw [same]
    exact keeps middle reached
  cases query with
  | inl coin=>exact prior _ (by trivial) result supported
  | inr command=>cases command with
    | bundle _ | build _ _=>exact allowed.elim
    | serverSend key bytes=>exact gated _ (fun middle reached=>prior (.inr (.serverSend key bytes)) (by trivial) middle reached) result supported
    | beaconSend owner bytes=>exact gated _ (fun middle reached=>prior (.inr (.beaconSend owner bytes)) (by trivial) middle reached) result supported
    | _=>exact prior _ (by trivial) result supported

omit [PublicWrapperPlatform.CryptoOperations] in
theorem typed (query :RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed :Quiet query)
    (before :Native×P) (result :RegistrationNativeRawAdapter.TypedSpec.Range query×(Native×P))
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential query).run before)) :
    result.2.1.server.world.world.2=before.1.server.world.world.2 :=by
  simp only [RegistrationNativePlatformPublicAdapterAuditModel.typed,RegistrationNativePlatformPackedState.pack,StateT.run,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact handler configuration created credential query allowed before.1 before.2 inner called

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame.handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame.typed
