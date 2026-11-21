import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback
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
local notation "Log"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential

/- The source callback verdict is charged to the typed authentication attempt on that same callback. -/
local notation "State"=>RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential
local notation "lowModel"=>RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration created credential
local notation "calls"=>RegistrationNativePlatformPublicAdapterDispatcher.calls (n:=n) configuration created credential

omit [PublicWrapperPlatform.CryptoOperations] in
theorem selected (query :RegistrationNativeInterface.Spec.Domain) (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain)
    (observe :RegistrationNativeRawAdapter.TypedSpec.Range chosen→RegistrationNativeInterface.Spec.Range query)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query=.query chosen observe)
    (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (result :RegistrationNativeInterface.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run before)) :
    ∃reply,result.1=observe reply ∧(reply,result.2.1)∈support ((typed chosen).run before.1) ∧
      result.2.2.calls=before.2.calls++[⟨chosen,before.1,reply,result.2.1⟩] :=by
  unfold RegistrationNativePlatformPublicAdapterAuditModel.raw at supported
  rw [RegistrationNativePlatformPublicAdapterTypedAuditRaw.query] at supported
  simp only [shape,support_map] at supported
  obtain ⟨middle,called,same⟩:=supported
  simp only [RegistrationNativePlatformPublicAdapterTypedAudit.handler,StateT.run,support_map] at called
  obtain ⟨actual,called,retained⟩:=called
  subst middle
  subst result
  exact ⟨actual.1,rfl,called,rfl⟩

theorem model (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :State)
    (result :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×State)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential query).run before)) :
    (result.1,result.2.1.1)∈support ((lowModel query).run before.1.1) :=by
  have erased:=RegistrationNativePlatformPublicAdapterLoggedCommon.query_erase Private lowModel calls physical
    (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential) query before
  have native:=RegistrationNativePlatformExtractedSdkPublic.query Private lowModel calls query before.1
  rw [←erased] at native
  change _=(lowModel query).run before.1.1 at native
  rw [←native,support_map]
  refine ⟨(result.1,result.2.1),?_,rfl⟩
  rw [support_map]
  exact ⟨result,supported,rfl⟩

omit [PublicWrapperPlatform.CryptoOperations] in
theorem raw_keep (query :RegistrationNativeInterface.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (result :RegistrationNativeInterface.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run before))
    (entry :RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source×P))
    (held :entry∈before.2.calls) :entry∈result.2.2.calls :=by
  have original:=supported
  unfold RegistrationNativePlatformPublicAdapterAuditModel.raw at supported
  rw [RegistrationNativePlatformPublicAdapterTypedAuditRaw.query] at supported
  cases form:RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query with
  | pure value=>
    simp only [form,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact held
  | query chosen observe=>
    obtain ⟨reply,_observed,_called,appended⟩:=selected configuration created credential query chosen observe form before result original
    rw [appended]
    exact List.mem_append_left _ held

omit [PublicWrapperPlatform.CryptoOperations] in
theorem low_keep (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (result :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (supported :result∈support ((lowModel query).run before))
    (entry :RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source×P))
    (held :entry∈before.2.calls) :entry∈result.2.2.calls :=by
  cases query with
  | inl publicQuery=>
    have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
      (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential publicQuery)) supported
    cases publicQuery with
    | inl coin=>exact raw_keep configuration created credential (.inl coin) before result actual entry held
    | inr command=>exact raw_keep configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command)) before result actual entry held
  | inr refused=>cases refused with
    | serverSend key bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.server_query configuration created credential key bytes oversized)) supported
      exact raw_keep configuration created credential (.inr (.serverSend key bytes)) before result actual entry held
    | beaconSend owner bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.beacon_query configuration created credential owner bytes oversized)) supported
      exact raw_keep configuration created credential (.inr (.beaconSend owner bytes)) before result actual entry held

theorem path_keep {before after :State} {entries :List (RegistrationNativeStageTrace.Call RegistrationNativePlatformPublicAdapterLowSpec.Spec State)}
    (actual :RegistrationNativeStageTrace.Path (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential) before entries after)
    (entry :RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source×P))
    (held :entry∈before.1.1.2.calls) :entry∈after.1.1.2.calls :=by
  induction actual with
  | nil=>exact held
  | cons call executed rest last following ih=>
    exact ih (low_keep configuration created credential call.query call.before.1.1 (call.reply,call.after.1.1)
      (model configuration created credential call.query call.before (call.reply,call.after) executed) entry held)

theorem public_selected (command :RegistrationNativePlatformPublicAdapterInterface.Command)
    (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain)
    (observe :RegistrationNativeRawAdapter.TypedSpec.Range chosen→RegistrationNativePlatformPublicAdapterInterface.CommandSpec.Range command)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire
      (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command))=.query chosen observe)
    (before after :State) (reply :RegistrationNativePlatformPublicAdapterInterface.CommandSpec.Range command)
    (executed :RegistrationNativeStageTrace.Executed (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential)
      ⟨.inl (.inr command),before,reply,after⟩) :
    ∃actual,reply=observe actual ∧(actual,after.1.1.1)∈support ((typed chosen).run before.1.1.1) ∧
      after.1.1.2.calls=before.1.1.2.calls++[⟨chosen,before.1.1.1,actual,after.1.1.1⟩] :=by
  have native:=model configuration created credential (.inl (.inr command)) before (reply,after) executed
  have original:=Eq.mp (congrArg (fun action=>(reply,after.1.1)∈support (action.run before.1.1))
    (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential (.inr command))) native
  change (reply,after.1.1)∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential
    (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command))).run before.1.1) at original
  exact selected configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command)) chosen observe shape before.1.1 (reply,after.1.1) original

theorem finish (before after :State) (index :Nat) (input :Slice U8) (packet :registration.ResponsePacket)
    (application :Pqxdh.Bytes)
    (decoded :RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)=some packet)
    (executed :RegistrationNativeStageTrace.Executed (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential)
      ⟨.inl (.inr (.finish index input)),before,some application,after⟩) :
    (⟨.inr (.finish index (some packet)),before.1.1.1,RustM.ok (some application),after.1.1.1⟩ :
      RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source×P))∈after.1.1.2.calls :=by
  have shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire
      (.inr (.finish index (TranscriptAuthParts.absSlice input)))=
      .query (.inr (.finish index (some packet))) RegistrationNativeRawAdapter.resultOption :=by
    have read:RegistrationNativeWire.readResponse RegistrationNativeConcreteCodec.wire (TranscriptAuthParts.absSlice input)=some packet:=
      (RegistrationNativeConcreteReaders.response (TranscriptAuthParts.absSlice input)).trans decoded
    exact congrArg (fun response=>RegistrationNativePlatformPublicAdapterTypedAuditRaw.Form.query
      (spec:=RegistrationNativeRawAdapter.TypedSpec) (.inr (.finish index response)) RegistrationNativeRawAdapter.resultOption) read
  obtain ⟨actual,observed,_called,appended⟩:=public_selected configuration created credential (.finish index input)
    (.inr (.finish index (some packet))) RegistrationNativeRawAdapter.resultOption shape before after (some application) executed
  have same :actual=RustM.ok (some application) :=by
    cases actual with
    | fail error | div=>cases observed
    | ok value=>exact congrArg RustM.ok observed.symm
  rw [same] at appended
  rw [appended]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem build (before after :State) (handle :Nat) (payload :Option (Slice U8))
    (reply :Option PqxdhServerRegistrationPublication.Response)
    (executed :RegistrationNativeStageTrace.Executed (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential)
      ⟨.inl (.inr (.build handle payload)),before,reply,after⟩) :
    ∃actual :RustM (Option (U64×Pqxdh.Bytes)),reply=RegistrationNativeRawAdapter.responseOption actual ∧
      (actual,after.1.1.1)∈support ((typed (.inr (.build handle
        (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice))))).run before.1.1.1) ∧
      (⟨.inr (.build handle (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice))),
        before.1.1.1,actual,after.1.1.1⟩ :RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec
          (RegistrationNativeExperiment.State n KemSK source×P))∈after.1.1.2.calls :=by
  obtain ⟨actual,observed,called,appended⟩:=public_selected configuration created credential (.build handle payload)
    (.inr (.build handle (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice))))
    RegistrationNativeRawAdapter.responseOption rfl before after reply executed
  exact ⟨actual,observed,called,by rw [appended];exact List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.model

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.raw_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.raw_keep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.low_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.low_keep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.path_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.path_keep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.public_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.public_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback.build
