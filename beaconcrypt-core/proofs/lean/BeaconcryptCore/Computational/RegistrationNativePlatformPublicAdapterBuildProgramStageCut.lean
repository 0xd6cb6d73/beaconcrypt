-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInitialScope
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut
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

variable {R A :Type}
local notation "Events" => RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

variable (originalLocal :LocalOperations (RustT (StateT P ProbComp))) (original :ContainerOperations (RustT (StateT P ProbComp)))
variable (previousCrypto :CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (previousChildren :ChildOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (fallback :registration.MldsaSigningRequest→StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp) RegistrationSigningShared.SignReply)


noncomputable def interpreter :QueryImpl RegistrationNativePlatformPublicAdapterBuildProgram.Spec (StateT (Cut×Events) Base):=
  RegistrationNativePlatformPublicAdapterBuildProgramStages.native RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback
noncomputable def actual :QueryImpl RegistrationNativePlatformPublicAdapterBuildProgram.Spec (StateT ((Cut×Events)×P) ProbComp):=
  fun query=>RegistrationNativePlatformPackedState.pack (interpreter coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query)

theorem call (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) (before :Cut) (previous :P) (prior :Events)
    (result :(((Word×Cut)×P)×Events))
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBuildProgramStages.sample
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous prior))
    (suffix :List Stage) (observed :result.2=prior++suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :Stage.sign request payload digest signature∈suffix) :
    ∃(leading trailing :List (RegistrationNativeStageTrace.Call RegistrationNativePlatformPublicAdapterBuildProgram.Spec ((Cut×Events)×P)))
      (call :RegistrationNativeStageTrace.Call RegistrationNativePlatformPublicAdapterBuildProgram.Spec ((Cut×Events)×P)),
      RegistrationNativeStageTrace.Path (actual (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) ((before,prior),previous) leading call.before ∧
      RegistrationNativeStageTrace.Executed (actual (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) call ∧
      RegistrationNativeStageTrace.Path (actual (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) call.after trailing ((result.1.1.2,result.2),result.1.2) ∧
      ∃current initial,call.query=.inr (.inr (.inr (current,initial))) ∧current.control=self.control ∧
      (∃pin availability application,
        registration.begin_server_completion self.control pin availability token.registration.agreement application=.ok (.Ok initial)) ∧
      ∃emitted,call.after.1.2=call.before.1.2++emitted ∧
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (Stage.sign request payload digest signature)∈emitted :=by
  have packed :(result.1.1.1,((result.1.1.2,result.2),result.1.2))∈support
      ((simulateQ (actual (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run ((before,prior),previous)) :=by
    simp only [RegistrationNativePlatformPublicAdapterBuildProgramStages.sample,support_map] at supported
    obtain ⟨inner,called,same⟩:=supported
    cases same
    unfold actual
    rw [←RegistrationNativePlatformPackedState.simulate_pack]
    simp only [RegistrationNativePlatformPackedState.pack,StateT.run,support_map]
    exact ⟨inner,called,rfl⟩
  have appends :∀(query :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain) (current :(Cut×Events)×P)
      (outcome :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range query×((Cut×Events)×P)),outcome∈support (((actual (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) query).run current)→
      ∃emitted,outcome.2.1.2=current.1.2++emitted :=by
    intro query current outcome called
    simp only [actual,RegistrationNativePlatformPackedState.pack,StateT.run,support_map] at called
    obtain ⟨raw,supported,same⟩:=called
    cases same
    obtain ⟨middle,observed⟩:=RegistrationNativePlatformPublicAdapterBuildSigningDelta.query_delta coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query current.1 current.2 raw supported
    exact ⟨middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage,observed⟩
  have quiet :∀(query :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain),¬¬RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix query→∀(current :(Cut×Events)×P)
      (outcome :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range query×((Cut×Events)×P)),
      outcome∈support (((actual (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) query).run current)→ outcome.2.1.2=current.1.2 :=by
    classical
    intro query permitted current outcome called
    simp only [actual,RegistrationNativePlatformPackedState.pack,StateT.run,support_map] at called
    obtain ⟨raw,supported,same⟩:=called
    cases same
    exact RegistrationNativePlatformPublicAdapterBuildSigningDelta.prefix_log coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query (not_not.mp permitted) current.1 current.2 raw supported
  obtain ⟨leading,trailing,call,beforePath,called,afterPath,allowed,marked,emitted,logEq,seen⟩:=
    RegistrationNativePlatformPublicAdapterSourceLogCrossing.crossing (actual (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) (fun current=>current.1.2) appends
      (RegistrationNativePlatformPublicAdapterBuildInitialScope.Allowed token self.control)
      (fun query=>¬RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix query) quiet
      (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data) (RegistrationNativePlatformPublicAdapterBuildInitialScope.program self token data)
      ((before,prior),previous) _ packed (suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage) observed
      (RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (Stage.sign request payload digest signature))
      (List.mem_map.mpr ⟨_,present,rfl⟩)
  refine ⟨leading,trailing,call,beforePath,called,afterPath,?_⟩
  cases queryEq:call.query with
  | inl self=>
    simp only [RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix,queryEq] at marked
    exact False.elim (marked True.intro)
  | inr query=>cases query with
    | inl pair=>
      simp only [RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix,queryEq] at marked
      exact False.elim (marked True.intro)
    | inr query=>cases query with
      | inl known=>
        simp only [RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix,queryEq] at marked
        exact False.elim (marked True.intro)
      | inr pair=>
        simp only [RegistrationNativePlatformPublicAdapterBuildInitialScope.Allowed,queryEq] at allowed
        exact ⟨pair.1,pair.2,rfl,allowed.1,allowed.2,emitted,logEq,seen⟩


theorem complete_cut (current :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (before :Cut) (previous :P) (prior suffix :Events)
    (result :((Publication×RustM AdapterPublicServerBuildBody.Reply)×(Cut×Events))×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.nativeComplete
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer original current initial).run (before,prior)).run previous))
    (observed :result.1.2.2=prior++suffix)
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (Stage.sign request payload digest signature)∈suffix) :
    ∃hashed firstState firstPlatform hashRequest hashState hashPlatform signState signPlatform,
      ((.ok (.Ok hashed),firstState),firstPlatform)∈support
        (((RegistrationNativePlatformPublicAdapterBuildStageCut.lifted (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer) (.inl initial)).run before).run previous) ∧
      hashed.request=.ok hashRequest ∧
      ((digest,hashState),hashPlatform)∈support
        (((RegistrationNativePlatformPublicAdapterBuildStageCut.lifted (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer) (.inr (.inl (.hash hashRequest)))).run firstState).run firstPlatform) ∧
      ((signature,signState),signPlatform)∈support
        (((RegistrationNativePlatformPublicAdapterBuildStageCut.lifted (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer) (.inr (.inl (.sign request payload digest)))).run hashState).run hashPlatform) ∧
      payload=RegistrationSigningTrace.Command.payload (.server hashed) ∧request.public_key=hashed.binding.server_pin.public_key ∧
      suffix=[RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (.firstRecord initial (.ok (.Ok hashed))),
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (.hash hashRequest digest),
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (.sign request payload digest signature)] :=by
  let :ContainerOperations (RustT Base):=original
  change result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))
      (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run (before,prior) >>=fun published=>do
        let word←AdapterPublicServerPublication.afterPublication (m:=Base) current published.1
        pure ((published.1,word),published.2)).run previous) at supported
  simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨published,called,word,_installed,same⟩:=supported
  cases same
  exact RegistrationNativePlatformPublicAdapterBuildSampleStageCut.nested_emitted_cut
    RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
    (fun _ _ same=>RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage.inj same)
    initial before previous prior suffix published called observed request payload digest signature present

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut.call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut.call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut.complete_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut.complete_cut
