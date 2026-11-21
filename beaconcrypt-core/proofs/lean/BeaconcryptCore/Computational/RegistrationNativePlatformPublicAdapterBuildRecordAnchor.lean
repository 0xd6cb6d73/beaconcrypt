-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFinishContents
/-! The actual emitted source first-record stage supplies its concrete allocator/AEAD/hash/raw-writer path at the same later cache. The remaining hash/sign/writer continuation is retained, so later failure does not lose the earlier record or its cache anchor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable [primitive :AdapterSealPrimitive.Operations]
variable {n :Nat} {I KemSK E P Log :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire)
variable (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
variable (allocation :RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (erased :commitment.CommitmentTranscript)
variable (rawAllocation :alloc.vec.Vec U8→Usize→StateT P ProbComp (RustM (core.result.Result Unit E)))
variable (serializer :U64→U64→Std.Array (Slice U8) 3#usize→Slice U8→StateT P ProbComp (RustM (Usize×Slice U8)))
variable (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
variable (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "Cut"=>RegistrationNativePlatformCutJournal.State Native
local notation "codec"=>RegistrationNativeWire.ledgerCodec wire
local notation "helper"=>AdapterRecordRawBytes.helper rawAllocation serializer
local notation "nested"=>RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
  (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer)
local notation "Publication"=>RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))

theorem first (initial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
    (before after :Cut) (previous next :P)
    (supported :((.ok (.Ok hashed),after),next)∈support (((nested (.inl initial)).run before).run previous)) :
    RegistrationServerRecordExecutor.Path initial hashed ∧
    RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup wire keyView failure allocation erased rawAllocation serializer
      initial hashed (RegistrationNativeWorldCache.cache after.1) :=by
  have law:=RegistrationNativePlatformPublicAdapterBuildStageCut.query_source
    (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer)
    (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer)
    id (fun _ _=>id_map _) (.inl initial) before
  simp only [id_eq] at law
  have projected :((.ok (.Ok hashed),after.1),next)∈support
      (((RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer (.inl initial)).run before.1).run previous):=by
    rw [←law,StateT.run_map,support_map]
    exact ⟨((.ok (.Ok hashed),after),next),supported,rfl⟩
  change ((.ok (.Ok hashed),after.1),next)∈support (((AdapterPublicServerLocalLens.localState
    (RegistrationNativePlatformSourceSealTrace.record coins setup codec keyView failure allocation erased helper initial)).run before.1).run previous) at projected
  rw [AdapterPublicServerLocalLens.local_run,StateT.run_map,support_map] at projected
  obtain ⟨raw,called,same⟩:=projected
  have replyEq:raw.1.1=.ok (.Ok hashed):=congrArg (fun value=>value.1.1) same
  have localEq:raw.1.2=after.1.server.world:=congrArg (fun value=>value.1.2.server.world) same
  have platformEq:raw.2=next:=congrArg Prod.snd same
  have actual :(.ok (.Ok hashed),(after.1.server.world,next))∈support
      ((RegistrationNativePlatformSourceSealTrace.joint (RegistrationNativePlatformSourceSealTrace.record coins setup codec keyView failure allocation erased helper initial)).run (before.1.server.world,previous)):=by
    apply (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mpr
    have rawEq:raw=((.ok (.Ok hashed),after.1.server.world),next):=Prod.ext (Prod.ext replyEq localEq) platformEq
    exact rawEq ▸called
  obtain ⟨trace⟩:=RegistrationNativePlatformSourceSealTrace.run coins setup codec keyView failure allocation erased helper initial hashed _ _ actual
  exact ⟨trace.path,⟨_,_,actual,le_refl _⟩⟩

theorem code (note :Stage→Log) (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
    (before :Cut) (previous :P) (past suffix :List Log)
    (result :(Publication×(Cut×List Log))×P)
    (supported :result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded nested
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
      (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run (before,past)).run previous))
    (observed :result.1.2.2=past++suffix)
    (present :note (.firstRecord initial (.ok (.Ok hashed)))∈suffix) :
    RegistrationServerRecordExecutor.Path initial hashed ∧
    RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup wire keyView failure allocation erased rawAllocation serializer
      initial hashed (RegistrationNativeWorldCache.cache result.1.2.1.1) :=by
  obtain ⟨firstState,firstPlatform,firstCalled,later⟩:=RegistrationNativePlatformPublicAdapterBuildFirstContinuation.nested_first_cut note nested
    injective initial hashed before previous past suffix result supported observed present
  obtain ⟨path,cut⟩:=first coins setup wire keyView failure allocation erased rawAllocation serializer sign writer initial hashed
    before firstState previous firstPlatform firstCalled
  have extension:=RegistrationNativePlatformPublicAdapterBuildCacheFrame.program coins setup codec keyView failure allocation helper erased sign writer
    note (RegistrationNativePlatformPublicAdapterBuildFirstContinuation.tailCode hashed)
    (firstState,past++[note (.firstRecord initial (.ok (.Ok hashed)))]) firstPlatform result later
  obtain ⟨recordBefore,recordAfter,recorded,anchor⟩:=cut
  exact ⟨path,⟨recordBefore,recordAfter,recorded,anchor.trans extension⟩⟩

section Complete
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]

theorem complete (note :Stage→Log) (injective :Function.Injective note)
    (original :ContainerOperations (RustT (StateT P ProbComp)))
    (current :beaconcrypt_public_wrapper.server.Server)
    (initial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
    (before :Cut) (previous :P) (past suffix :List Log)
    (result :((Publication×RustM AdapterPublicServerBuildBody.Reply)×(Cut×List Log))×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.nativeComplete
      note coins setup codec keyView failure allocation helper erased sign writer original current initial).run (before,past)).run previous))
    (observed :result.1.2.2=past++suffix)
    (present :note (.firstRecord initial (.ok (.Ok hashed)))∈suffix) :
    RegistrationServerRecordExecutor.Path initial hashed ∧
    RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup wire keyView failure allocation erased rawAllocation serializer
      initial hashed (RegistrationNativeWorldCache.cache result.1.2.1.1) :=by
  let :ContainerOperations (RustT (StateT P ProbComp)):=original
  change result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded nested
    (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
    (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run (before,past) >>=fun published=>do
      let word←AdapterPublicServerPublication.afterPublication (m:=StateT P ProbComp) current published.1
      pure ((published.1,word),published.2)).run previous) at supported
  simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨published,called,word,_installed,same⟩:=supported
  cases same
  exact code coins setup wire keyView failure allocation erased rawAllocation serializer sign writer
    note injective initial hashed before previous past suffix published called observed present
end Complete

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor.first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor.code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor.code

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor.complete
