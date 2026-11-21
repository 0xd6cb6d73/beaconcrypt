-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization
/-! The actual Builder prefix and source installer enclose the jointly observed first-record/signing suffix. Readonly lookup and all allocator refusals execute unchanged. Observations survive the actual returned source Server, even when the response writer or subsequent source map installation fails. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildTrace (Publication Word)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
abbrev Spec := RegistrationNativePlatformPublicAdapterBuildProgram.Spec
variable {Log : Type}
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {Reader Response : Type}
variable {mlSource : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT P ProbComp
local notation "SourceM" => StateT Cut Base

open RegistrationNativePlatformPublicAdapterBundleSigningDelta (history)
open RegistrationNativePlatformPublicAdapterSourceSigningHistory (receipts)
open RegistrationNativePlatformPublicAdapterSourceAuthentication (stages)
variable {R A :Type}
local notation "Events" => RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

omit material platform ed primitive [PublicWrapperPlatform.Allocator] in
theorem outgoing (query :RegistrationSigningShared.Spec.Domain) (before :Native) (previous :P)
    (result :(RegistrationSigningShared.Spec.Range query×Native)×P)
    (supported :result∈support (((AdapterPublicServerCompletionNative.outgoing coins sign query).run before).run previous)) :
    history result.1.2=history before++receipts
      (RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation query result.1.1) :=by
  rw [AdapterPublicServerCompletionNative.outgoing,AdapterPublicServerLocalLens.local_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  change inner.1.2.world.2=before.server.world.world.2++receipts
    (RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation query inner.1.1)
  have actual:=RegistrationNativePlatformHashReceipt.native_support coins _ inner.1 previous inner.2 called
  cases query with
  | hash request=>
    simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing,RegistrationWorldSigning.outgoing,StateT.run,
      Functor.map_map,support_map] at actual
    obtain ⟨response,_called,same⟩:=actual
    have kept:=(congrArg (fun value=>value.2.world.2) same).symm
    simpa only [history,AdapterPublicServerLocalLens.putLocal,
      RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation,receipts,List.filterMap_cons,List.filterMap_nil,
      RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipt,List.append_nil] using kept
  | sign request payload digest=>
    simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing,RegistrationWorldSigning.outgoing,StateT.run,
      Functor.map_map,support_map] at actual
    obtain ⟨response,_called,same⟩:=actual
    have kept:=(congrArg (fun value=>value.2.world.2) same).symm
    have replyEq:=congrArg Prod.fst same
    change response.1=inner.1.1 at replyEq
    change inner.1.2.world.2=before.server.world.world.2++
      [⟨⟨request.public_key,payload,RegistrationSigningTrace.replyBytes response.1⟩,digest⟩] at kept
    rw [replyEq] at kept
    simpa only [history,AdapterPublicServerLocalLens.putLocal,
      RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation,receipts,List.filterMap_cons,List.filterMap_nil,
      RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipt] using kept


omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem leaf (query :RegistrationNativePlatformPublicAdapterBuildStages.Spec.Domain) (before :Native) (previous :P)
    (result :(RegistrationNativePlatformPublicAdapterBuildStages.Spec.Range query×Native)×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer query).run before).run previous)) :
    history result.1.2=history before++receipts
      (RegistrationNativePlatformPublicAdapterBuildStages.observation query result.1.1) :=by
  cases query with
  | inl initial=>
    change result∈support (((AdapterPublicServerLocalLens.localState
      (RegistrationNativePlatformSourceSealTrace.record coins setup codec keyView failure allocation erased helper initial)).run before).run previous) at supported
    rw [AdapterPublicServerLocalLens.local_run,StateT.run_map,support_map] at supported
    obtain ⟨inner,called,same⟩:=supported
    cases same
    have kept:=(RegistrationNativePlatformSourceFrames.record_frame coins setup codec keyView failure allocation erased helper initial before.server.world previous inner.1 inner.2 called).2
    simpa only [history,AdapterPublicServerLocalLens.putLocal,
      RegistrationNativePlatformPublicAdapterBuildStages.observation,receipts,List.filterMap_cons,List.filterMap_nil,
      RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipt,List.append_nil] using kept
  | inr query=>cases query with
    | inl request=>exact outgoing coins sign request before previous result supported
    | inr signed=>
      change result∈support (((AdapterPublicServerSigningNative.encoder (AdapterPublicServerCompletionNative.writer writer) signed).run before).run previous) at supported
      rw [AdapterPublicServerCompletionNative.encoder_source,AdapterPublicServerLocalLens.local_run,
        RegistrationNativePlatformSourceBuild.encode,StateT.run_lift,bind_pure_comp,
        StateT.run_map,support_map] at supported
      obtain ⟨inner,called,same⟩:=supported
      cases same
      rw [StateT.run_map,support_map] at called
      obtain ⟨response,_possible,same⟩:=called
      cases same
      simp only [history,AdapterPublicServerLocalLens.putLocal,
        RegistrationNativePlatformPublicAdapterBuildStages.observation,receipts,List.filterMap_nil,List.append_nil]


def Aligned (before :Cut×Events):Prop:=history before.1.1=receipts (stages before.2)

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem lifted (query :RegistrationNativePlatformPublicAdapterBuildStages.Spec.Domain) (before :Cut) (previous :P)
    (result :(RegistrationNativePlatformPublicAdapterBuildStages.Spec.Range query×Cut)×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
      (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer) query).run before).run previous)) :
    history result.1.2.1=history before.1++receipts
      (RegistrationNativePlatformPublicAdapterBuildStages.observation query result.1.1) :=by
  have law:=RegistrationNativePlatformPublicAdapterBuildStageCut.query_source
    (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer)
    (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer)
    id (fun _ _=>id_map _) query before
  simp only [id_eq] at law
  have projected :((result.1.1,result.1.2.1),result.2)∈support
      (((RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer query).run before.1).run previous) :=by
    rw [←law,StateT.run_map,support_map]
    exact ⟨result,supported,rfl⟩
  exact leaf coins setup codec keyView failure allocation helper erased sign writer query before.1 previous _ projected

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem query (query :RegistrationNativePlatformPublicAdapterBuildStages.Spec.Domain) (before :Cut×Events) (previous :P)
    (aligned :Aligned before)
    (result :((RegistrationNativePlatformPublicAdapterBuildStages.Spec.Range query×(Cut×Events))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage) query).run before).run previous)) :
    Aligned result.1.2 :=by
  change result∈support (((fun inner=>(inner.1,(inner.2,before.2++
    (RegistrationNativePlatformPublicAdapterBuildStages.observation query inner.1).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))) <$>
    (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
      (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer) query).run before.1).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  unfold Aligned
  rw [RegistrationNativePlatformPublicAdapterBundleSigningDelta.append_log,
    lifted coins setup codec keyView failure allocation helper erased sign writer query before.1 previous inner called,aligned]

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem program (work :OracleComp RegistrationNativePlatformPublicAdapterBuildStages.Spec A)
    (before :Cut×Events) (previous :P) (aligned :Aligned before)
    (result :(A×(Cut×Events))×P)
    (supported :result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)) work).run before).run previous)) :
    Aligned result.1.2 :=by
  exact RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ Aligned
    (query coins setup codec keyView failure allocation helper erased sign writer) work before previous aligned result supported


theorem complete (original :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (before :Cut×Events) (previous :P) (aligned :Aligned before)
    (result :((Publication×RustM AdapterPublicServerBuildBody.Reply)×(Cut×Events))×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.nativeComplete
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer original self initial).run before).run previous)) :
    Aligned result.1.2 :=by
  let :ContainerOperations (RustT Base):=original
  change result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))
      (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run before >>=fun published=>do
        let word←AdapterPublicServerPublication.afterPublication (m:=Base) self published.1
        pure ((published.1,word),published.2)).run previous) at supported
  simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨published,called,word,_installed,same⟩:=supported
  cases same
  exact program coins setup codec keyView failure allocation helper erased sign writer _ before previous aligned published called


variable (originalLocal :LocalOperations (RustT (StateT P ProbComp))) (original :ContainerOperations (RustT (StateT P ProbComp)))
variable (previousCrypto :CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (previousChildren :ChildOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (fallback :registration.MldsaSigningRequest→StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp) RegistrationSigningShared.SignReply)

theorem prefix_query (request :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (allowed :RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix request)
    (before :Cut×Events) (previous :P) (aligned :Aligned before)
    (result :((RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range request×(Cut×Events))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before).run previous)) :
    Aligned result.1.2 :=by
  have same :RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request =
      (fun (before :Cut×Events)=> (fun inner=>(inner.1,(inner.2,before.2))) <$>
        (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before.1) :=by
    cases request with
    | inl self=>rfl
    | inr request=>cases request with
      | inl pair=>rfl
      | inr request=>cases request with
        | inl known=>rfl
        | inr pair=>cases allowed
  rw [same] at supported
  change result∈support (((fun inner=>(inner.1,(inner.2,before.2))) <$>
    (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before.1).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact (RegistrationNativePlatformPublicAdapterBuildReceiptFrame.query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request allowed before.1 previous inner called).trans aligned

theorem program_query (request :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (before :Cut×Events) (previous :P) (aligned :Aligned before)
    (result :((RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range request×(Cut×Events))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before).run previous)) :
    Aligned result.1.2 :=by
  cases request with
  | inl self=>exact prefix_query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback (.inl self) True.intro before previous aligned result supported
  | inr request=>cases request with
    | inl pair=>exact prefix_query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback (.inr (.inl pair)) True.intro before previous aligned result supported
    | inr request=>cases request with
      | inl known=>exact prefix_query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback (.inr (.inr (.inl known))) True.intro before previous aligned result supported
      | inr pair=>exact complete coins setup codec keyView failure allocation helper erased sign writer original pair.1 pair.2 before previous aligned result supported

theorem whole_program (work :OracleComp RegistrationNativePlatformPublicAdapterBuildProgram.Spec A)
    (before :Cut×Events) (previous :P) (aligned :Aligned before)
    (result :(A×(Cut×Events))×P)
    (supported :result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) work).run before).run previous)) :
    Aligned result.1.2 :=by
  exact RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ Aligned
    (program_query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) work before previous aligned result supported

theorem sample (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) (before :Cut) (previous :P) (prior :Events) (aligned :Aligned (before,prior))
    (result :(((Word×Cut)×P)×Events))
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBuildProgramStages.sample
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous prior)) :
    history result.1.1.2.1=receipts (stages result.2) :=by
  simp only [RegistrationNativePlatformPublicAdapterBuildProgramStages.sample,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact whole_program coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback _ (before,prior) previous aligned inner called

theorem sample_project (control :pqxdh.ServerState)
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) (before :Cut) (previous :P) (prior :Events) (aligned :Aligned (before,prior))
    (result :(((Word×Cut)×P)×Events))
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBuildProgramStages.sample
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous prior)) :
    (AdapterPublicServerBuildPrefix.project control result.1.1).2.server.world.world.2=receipts (stages result.2) :=by
  exact (RegistrationNativePlatformPublicAdapterBuildReceiptFrame.build_project control result.1.1).trans
    (sample coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous prior aligned result supported)


private def Extension (prior current :Events):Prop:=
  ∃suffix :List Stage,current=prior++suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem observed_extension {Q S X :Type} {spec :OracleSpec Q}
    (implementation :QueryImpl spec (StateT S Base))
    (observe :(query :spec.Domain)→spec.Range query→List Stage)
    (work :OracleComp spec X) (prior :Events) (before :S×Events) (previous :P)
    (held :Extension prior before.2) (result :(X×(S×Events))×P)
    (supported :result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded implementation
      (fun query reply=>(observe query reply).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)) work).run before).run previous)) :
    Extension prior result.1.2.2 :=by
  apply RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ (fun current=>Extension prior current.2) _ work before previous held result supported
  intro query current previous held result supported
  change result∈support (((fun inner=>(inner.1,(inner.2,current.2++(observe query inner.1).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))) <$>
    (implementation query).run current.1).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,same⟩:=supported
  cases same
  obtain ⟨leading,kept⟩:=held
  refine ⟨leading++observe query inner.1.1,?_⟩
  simp only [kept,List.map_append,List.append_assoc]

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem lifted_extension {X :Type} (work :StateT Cut Base X)
    (prior :Events) (before :Cut×Events) (previous :P) (held :Extension prior before.2)
    (result :(X×(Cut×Events))×P)
    (supported :result∈support (((fun (current :Cut×Events)=>(fun inner=>(inner.1,(inner.2,current.2))) <$>work.run current.1) before).run previous)) :
    Extension prior result.1.2.2 :=by
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,same⟩:=supported
  cases same
  exact held

private theorem complete_extension
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (prior :Events) (before :Cut×Events) (previous :P) (held :Extension prior before.2)
    (result :((Publication×RustM AdapterPublicServerBuildBody.Reply)×(Cut×Events))×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.nativeComplete
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer original self initial).run before).run previous)) :
    Extension prior result.1.2.2 :=by
  let :ContainerOperations (RustT Base):=original
  change result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))
      (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run before >>=fun published=>do
        let word←AdapterPublicServerPublication.afterPublication (m:=Base) self published.1
        pure ((published.1,word),published.2)).run previous) at supported
  simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨published,called,word,_installed,same⟩:=supported
  cases same
  exact observed_extension _ _ _ prior before previous held published called

private theorem extension_query (request :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (prior :Events) (before :Cut×Events) (previous :P) (held :Extension prior before.2)
    (result :((RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range request×(Cut×Events))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before).run previous)) :
    Extension prior result.1.2.2 :=by
  cases request with
  | inl self=>exact lifted_extension _ prior before previous held result supported
  | inr request=>cases request with
    | inl pair=>exact lifted_extension _ prior before previous held result supported
    | inr request=>cases request with
      | inl known=>exact lifted_extension _ prior before previous held result supported
      | inr pair=>exact complete_extension coins setup codec keyView failure allocation helper erased sign writer original pair.1 pair.2 prior before previous held result supported

theorem sample_delta (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) (before :Cut) (previous :P) (prior :Events)
    (result :(((Word×Cut)×P)×Events))
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBuildProgramStages.sample
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous prior)) :
    ∃middle :List Stage,result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  simp only [RegistrationNativePlatformPublicAdapterBuildProgramStages.sample,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ (fun current=>Extension prior current.2)
    (fun request=>extension_query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request prior)
    _ (before,prior) previous ⟨[],(List.append_nil prior).symm⟩ inner called


theorem query_delta (request :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (before :Cut×Events) (previous :P)
    (result :((RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range request×(Cut×Events))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before).run previous)) :
    ∃middle :List Stage,result.1.2.2=before.2++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  exact extension_query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request before.2 before previous ⟨[],(List.append_nil _).symm⟩ result supported

theorem prefix_log (request :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (allowed :RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix request)
    (before :Cut×Events) (previous :P)
    (result :((RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range request×(Cut×Events))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before).run previous)) :
    result.1.2.2=before.2 :=by
  have same :RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request =
      (fun (before :Cut×Events)=> (fun inner=>(inner.1,(inner.2,before.2))) <$>
        (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before.1) :=by
    cases request with
    | inl self=>rfl
    | inr request=>cases request with
      | inl pair=>rfl
      | inr request=>cases request with
        | inl known=>rfl
        | inr pair=>cases allowed
  rw [same] at supported
  change result∈support (((fun inner=>(inner.1,(inner.2,before.2))) <$>
    (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before.1).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.leaf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.lifted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.prefix_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.prefix_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.program_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.whole_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.whole_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample_delta

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.query_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.query_delta

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.prefix_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta.prefix_log
