-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning
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
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "Private"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential

local notation "serverReceipts"=>RegistrationNativeMldsaRoleFrame.serverReceipts
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential

def Quiet :RegistrationNativeInterface.Spec.Domain→Prop
  | .inr (.build _ _)=>False
  | _=>True

omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  [FrameDispatchFallback.Operations] originalGenerators originalCrypto originalLocal originalContainers in
private theorem form_quiet (wire :RegistrationNativeWire.Wire) (query :RegistrationNativeInterface.Spec.Domain) (allowed :Quiet query)
    (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain) (observe :RegistrationNativeRawAdapter.TypedSpec.Range chosen→RegistrationNativeInterface.Spec.Range query)
    (form :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form wire query=.query chosen observe) :
    RegistrationNativePlatformPublicAdapterServerReceiptFrame.Quiet chosen :=by
  cases query with
  | inl coin=>cases form;trivial
  | inr command=>cases command with
    | build _ _=>exact allowed.elim
    | create edPin mlPin keyId=>
      cases parsed:PqxdhDeploymentInterface.parsePin edPin <;>cases parsedMl:RegistrationNativeWire.parseMldsaPin mlPin <;>
        simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,parsed,parsedMl,reduceCtorEq] at form
      cases form
      trivial
    | accept bytes=>
      cases parsed:RegistrationNativeWire.readInit wire bytes <;>
        simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,parsed,reduceCtorEq] at form
      cases form
      trivial
    | _=>cases form;trivial

omit [PublicWrapperPlatform.CryptoOperations] in
theorem raw (query :RegistrationNativeInterface.Spec.Domain) (allowed :Quiet query)
    (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (result :RegistrationNativeInterface.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run before)) :
    serverReceipts result.2.1.1.server.world.world.2=serverReceipts before.1.1.server.world.world.2 :=by
  unfold RegistrationNativePlatformPublicAdapterAuditModel.raw at supported
  rw [RegistrationNativePlatformPublicAdapterTypedAuditRaw.query] at supported
  cases form:RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query with
  | pure value=>
    simp only [form,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    rfl
  | query chosen observe=>
    simp only [form,support_map] at supported
    obtain ⟨middle,called,same⟩:=supported
    simp only [RegistrationNativePlatformPublicAdapterTypedAudit.handler,StateT.run,support_map] at called
    obtain ⟨actual,called,retained⟩:=called
    subst middle
    subst result
    exact RegistrationNativePlatformPublicAdapterServerReceiptFrame.typed configuration created credential chosen
      (form_quiet RegistrationNativeConcreteCodec.wire query allowed chosen observe form) before.1 actual called

def NonBuild :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain→Prop
  | .inl (.inr (.build _ _))=>False
  | _=>True

omit [PublicWrapperPlatform.CryptoOperations] in
theorem low (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (allowed :NonBuild query)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (result :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential query).run before)) :
    serverReceipts result.2.1.1.server.world.world.2=serverReceipts before.1.1.server.world.world.2 :=by
  cases query with
  | inl publicQuery=>
    have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
      (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential publicQuery)) supported
    cases publicQuery with
    | inl coin=>exact raw configuration created credential (.inl coin) (by trivial) before result actual
    | inr command=>
      have quiet :Quiet (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command)) :=by
        cases command with
        | build _ _=>exact allowed.elim
        | _=>trivial
      exact raw configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command)) quiet before result actual
  | inr refused=>cases refused with
    | serverSend key bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.server_query configuration created credential key bytes oversized)) supported
      exact raw configuration created credential (.inr (.serverSend key bytes)) (by trivial) before result actual
    | beaconSend owner bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.beacon_query configuration created credential owner bytes oversized)) supported
      exact raw configuration created credential (.inr (.beaconSend owner bytes)) (by trivial) before result actual

theorem server_build (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformExtractedSdkPublic.State Private)
    (prior :RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P)
    (result :(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential query before.1 before.2).step.Packet×
      RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential query before prior).sample)
    (history :before.1.1.1.server.world.world.2=RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
      (RegistrationNativePlatformPublicAdapterSourceAuthentication.stages prior))
    (fresh :List RegistrationNativePlatformPublicAdapterSourceTrace.Stage)
    (logEq :result.2=prior++fresh.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload) (digest :CtxRomAuth.CtxDigest)
    (reply :RegistrationSigningShared.SignReply)
    (emitted :RegistrationNativePlatformPublicAdapterSourceTrace.Stage.sign request payload digest reply∈fresh)
    (role :payload.role=.server) :
    ∃handle data,query=.inl (.inr (.build handle data)) :=by
  classical
  by_contra absent
  have allowed :NonBuild query :=by
    cases query with
    | inr refused=>trivial
    | inl publicQuery=>cases publicQuery with
      | inl coin=>trivial
      | inr command=>cases command with
        | build handle data=>exact False.elim (absent ⟨handle,data,rfl⟩)
        | _=>trivial
  have native:=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.packet_native configuration created credential query before prior ⟨result,supported⟩
  have frame:=low configuration created credential query allowed before.1
    ((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential query before.1 before.2).step.native result.1) native
  have aligned:=RegistrationNativePlatformPublicAdapterSigningHistory.aligned configuration created credential query before prior history result supported
  have filtered :serverReceipts (RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
      (RegistrationNativePlatformPublicAdapterSourceAuthentication.stages result.2))=
      serverReceipts (RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
        (RegistrationNativePlatformPublicAdapterSourceAuthentication.stages prior)) :=
    (congrArg serverReceipts aligned).symm.trans (frame.trans (congrArg serverReceipts history))
  have stageAppend :RegistrationNativePlatformPublicAdapterSourceAuthentication.stages
      (prior++fresh.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)=
      RegistrationNativePlatformPublicAdapterSourceAuthentication.stages prior++fresh :=by
    simp only [RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_append,
      List.filterMap_map,List.filterMap_some,Function.comp_def]
  rw [logEq,stageAppend,RegistrationNativePlatformPublicAdapterSourceSigningHistory.append_receipts] at filtered
  unfold RegistrationNativeMldsaRoleFrame.serverReceipts at filtered
  rw [List.filter_append] at filtered
  have sizes:=congrArg List.length filtered
  simp only [List.length_append] at sizes
  have zero :(serverReceipts (RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts fresh)).length=0:=by
    dsimp only [RegistrationNativeMldsaRoleFrame.serverReceipts]
    omega
  have empty :serverReceipts (RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts fresh)=[]:=List.length_eq_zero_iff.mp zero
  let receipt :RegistrationSigningShared.Receipt:=⟨⟨request.public_key,payload,RegistrationSigningTrace.replyBytes reply⟩,digest⟩
  have captured :receipt∈RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts fresh :=
    List.mem_filterMap.mpr ⟨_,emitted,rfl⟩
  have recorded :receipt∈serverReceipts (RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts fresh):=by
    apply List.mem_filter.mpr
    exact ⟨captured,by simp only [receipt,role,decide_true]⟩
  rw [empty] at recorded
  cases recorded

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning.raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning.low' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning.low
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning.server_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning.server_build
