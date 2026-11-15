-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages
import BeaconcryptCore.Refinement.AdapterPublicServerRecordNative
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInstallLift
/-! The first-record observer is inserted at the actual source return before the source signing continuation. Its first action consists of the actual source record leaves, and the actual source signing and mutable installation continue in the same logged state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitive :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n :Nat} {I KemSK E P Log :Type} {base :OracleSpec I} {Reader Response :Type}
variable {mlSource :RegistrationNativeMldsa.Source}
local notation "Base"=>StateT P ProbComp
local notation "Physical"=>StateT (Backend n KemSK×List Log) Base
local notation "SourceM"=>StateT (RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) Base

private def lift {S A :Type} (work :StateT S Base A) :StateT (S×List Log) Base A:=fun before=>
  (fun result=>(result.1,(result.2,before.2))) <$>work.run before.1

private def embed {A :Type} (work :StateT (Backend n KemSK) Base A) :SourceM A:=fun before=>
  (fun result=>(result.1,((result.2,before.1.2),before.2))) <$>work.run before.1.1

noncomputable def outgoing
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec Physical:=
  RegistrationNativePlatformPublicAdapterSourceTrace.recorded
    (RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign)
    (fun query reply=>(RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation query reply).map note)

noncomputable def encoder (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (signed :registration.SignedResponseView) :Physical (RustM (core.option.Option (alloc.vec.Vec U8))):=
  AdapterPublicServerSigningNative.encoder (fun query=>StateT.lift (writer query)) signed

@[instance_reducible] noncomputable def localOperations
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) :LocalOperations (RustT SourceM):=
  AdapterPublicServerSigningNative.localOperations (outgoing note coins sign) fallback
    {RegistrationNativePlatformPublicAdapterLeaves.localOperations original with
      ratchet_initial_ratchet_hkdf:=fun request=>⟨RustM.ok <$>
        embed (RegistrationNativePlatformPublicAdapterBuildBackend.initial setup request)⟩
      ratchet_execute_seal_request:=fun request=>⟨embed (RegistrationNativePlatformPublicAdapterSealBackend.sealing coins setup codec keyView failure allocation request)⟩
      ratchet_execute_write_request:=fun request=>⟨embed (StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request))⟩}

@[instance_reducible] noncomputable def children
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (previous :ChildOperations (RustT SourceM)) :ChildOperations (RustT SourceM):=
  AdapterPublicServerSigningNative.children (outgoing note coins sign)
  {previous with
    ratchetHkdf:=fun request=>⟨RustM.ok <$>embed (RegistrationNativePlatformPublicAdapterBuildBackend.ratchet coins setup codec request)⟩
    commitmentHash:=fun transcript=>⟨embed (RegistrationNativePlatformPublicAdapterSealBackend.hash coins setup codec erased transcript)⟩
    } (fun query=>StateT.lift (writer query))

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem initial_callback (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (request :ratchet.InitialRatchetKdfRequest) :
    RegistrationNativePlatformPublicAdapterSealBackend.records (n:=n) coins setup codec (.initialKdf request)=
      (fun bytes=>core.option.Option.Some (⟨bytes⟩ :pqxdh.concrete.InitialRatchetKdfResponse)) <$>
        RegistrationNativePlatformPublicAdapterBuildBackend.initial (P:=P) setup request :=by
  apply StateT.ext
  intro before
  change simulateQ coins (pure (core.option.Option.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request),before))=pure _
  rw [simulateQ_pure]

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem ratchet_callback (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (request :ratchet.SymmetricRatchetKdfRequest) :
    RegistrationNativePlatformPublicAdapterSealBackend.records (n:=n) coins setup codec (.ratchetKdf request)=
      core.option.Option.Some <$>RegistrationNativePlatformPublicAdapterBuildBackend.ratchet coins setup codec request :=by
  apply StateT.ext
  intro before
  change simulateQ coins ((core.option.Option.Some <$>simulateQ
    (RegistrationNativePlatformPublicAdapterRecordBackend.shared setup codec)
    (MldsaSharedNative.recordLift (.inl request))).run before)=_
  simp only [MldsaSharedNative.recordLift,simulateQ_spec_query]
  change simulateQ coins ((core.option.Option.Some <$>
    RegistrationNativePlatformPublicAdapterRecordBackend.record setup codec (.inl request)).run before)=_
  rw [StateT.run_map,simulateQ_map]
  rfl

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem embed_pure {A :Type} (value :A) :
    embed (n:=n) (KemSK:=KemSK) (P:=P) (Log:=Log) (pure value)=pure value :=by
  apply StateT.ext
  intro before
  change (fun result=>(result.1,((result.2,before.1.2),before.2))) <$> (pure (value,before.1.1):Base _)=pure (value,before)
  rw [map_pure]

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem embed_bind {A B :Type} (work :StateT (Backend n KemSK) Base A)
    (next :A→StateT (Backend n KemSK) Base B) :
    embed (Log:=Log) (work>>=next)=(embed work>>=fun value=>embed (next value)) :=by
  apply StateT.ext
  intro before
  change (fun result=>(result.1,((result.2,before.1.2),before.2))) <$> (work>>=next).run before.1.1=(embed work>>=fun value=>embed (next value)).run before
  rw [StateT.run_bind,StateT.run_bind]
  simp only [embed,StateT.run]
  rw [map_bind,bind_map_left]

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem embed_hom :Cslib.IsMonadHom (StateT (Backend n KemSK) Base) SourceM
    (fun {A} (work :StateT (Backend n KemSK) Base A)=>embed (Log:=Log) work):=
  .mk' embed_pure embed_bind

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem borrow_seal {m :Type→Type} [Monad m] [LawfulMonad m]
    (work :m (RustM AdapterSealNative.Output)) :
    (do let detached←(⟨work⟩ :RustT m AdapterSealNative.Output)
        let borrowed←AdapterRecordRequestMonad.liftRust (core.option.Option.as_ref detached)
        AdapterPublicWrapperRequestMonad.Option.map
          beaconcrypt_public_request.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816 borrowed ()).run=work :=by
  simp only [RustT.run_bind,RustT.run_liftRust]
  conv_rhs=>rw [←bind_pure work]
  apply bind_congr
  intro result
  cases result with
  | fail error | div=>rfl
  | ok optional=>cases optional with
    | none=>simp only [core.option.Option.as_ref,pure_bind];rfl
    | some pair=>
      simp only [core.option.Option.as_ref,pure_bind,AdapterPublicWrapperRequestMonad.Option.map,
        RustT.run_bind,RustT.run_pure]
      simp only [AdapterPublicWrapperLiftFunction.call,AdapterPublicWrapperLiftFunction.LiftFunction.lift,
        AdapterRecordRequestMonad.liftRust,pure_bind]
      have closure :beaconcrypt_public_wrapper.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816.call_once () pair=.ok pair:=rfl
      rw [closure]

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem borrow_write {m :Type→Type} [Monad m] [LawfulMonad m]
    (work :m (RustM (core.option.Option (alloc.vec.Vec U8)))) :
    (do let output←(⟨work⟩ :RustT m (core.option.Option (alloc.vec.Vec U8)))
        AdapterRecordRequestMonad.liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) output)).run=work :=by
  simp only [RustT.run_bind,RustT.run_liftRust]
  conv_rhs=>rw [←bind_pure work]
  apply bind_congr
  intro result
  cases result with
  | fail error | div=>rfl
  | ok optional=>cases optional <;>rfl

noncomputable def kdf (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response) :
    AdapterPublicServerRecord.Kdf SourceM where
  initial request:=embed (RegistrationNativePlatformPublicAdapterBuildBackend.initial setup request)
  ratchet request:=embed (RegistrationNativePlatformPublicAdapterBuildBackend.ratchet coins setup codec request)

noncomputable def first
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (initial :registration.ServerInitialKdf) :SourceM (RustM RegistrationServerRecordExecutor.Result):=
  let :LocalOperations (RustT SourceM):=localOperations note coins setup codec keyView failure allocation helper sign fallback original
  let :ChildOperations (RustT SourceM):=children note coins setup codec erased sign writer previous
  RegistrationNativePlatformSourceRecord.fromInitialWithHash
    (AdapterPublicServerRecord.recordOperations (kdf coins setup codec))
    AdapterPublicServerRecord.sealLeaf
    (fun transcript=>(@ChildOperations.commitmentHash (RustT SourceM) inferInstance transcript).run)
    AdapterPublicServerRecord.writeLeaf initial


omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem first_congr {m :Type→Type} [Monad m]
    (left right :QueryImpl RegistrationRecordPrimitives.Spec m)
    (sameInitial :∀request,left (.initialKdf request)=right (.initialKdf request))
    (sameRatchet :∀request,left (.ratchetKdf request)=right (.ratchetKdf request))
    (sealing :record_effects.AeadSealRequest→m (RustM AdapterSealNative.Output))
    (hash :commitment.CommitmentTranscript→m RegistrationNativePlatformCommitment.HashReply)
    (write :record_effects.RecordWriteRequest→m (RustM (core.option.Option (Slice U8))))
    (initial :registration.ServerInitialKdf) :
    RegistrationNativePlatformSourceRecord.fromInitialWithHash left sealing hash write initial=
      RegistrationNativePlatformSourceRecord.fromInitialWithHash right sealing hash write initial:=by
  unfold RegistrationNativePlatformSourceRecord.fromInitialWithHash
  apply congrArg (RegistrationNativePlatformServerRecord.continueWith initial.request)
  funext request
  rw [sameInitial]
  apply bind_congr
  intro response
  apply congrArg (RegistrationNativePlatformServerRecord.continueResult (initial.resume response))
  funext pending
  unfold RegistrationNativePlatformSourceRecord.fromRatchetWithHash
  apply congrArg (RegistrationNativePlatformServerRecord.continueWith pending.request)
  funext request
  rw [sameRatchet]

omit ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem first_normalize
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (initial :registration.ServerInitialKdf) :
    first note coins setup codec keyView failure allocation helper erased sign fallback original previous writer initial=
      embed (Log:=Log) (RegistrationNativePlatformPublicAdapterBuildRecord.firstRecord coins setup codec keyView failure allocation helper erased initial) :=by
  let :LocalOperations (RustT SourceM):=localOperations note coins setup codec keyView failure allocation helper sign fallback original
  let :ChildOperations (RustT SourceM):=children note coins setup codec erased sign writer previous
  unfold first
  dsimp only
  have sealEq :AdapterPublicServerRecord.sealLeaf (m:=SourceM)=
      fun request=>embed (Log:=Log) (RegistrationNativePlatformPublicAdapterSealBackend.sealing coins setup codec keyView failure allocation request) :=by
    funext request
    exact borrow_seal _
  have writeEq :AdapterPublicServerRecord.writeLeaf (m:=SourceM)=
      fun request=>embed (Log:=Log) (StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request)) :=by
    funext request
    exact borrow_write _
  rw [sealEq,writeEq]
  have initialEq :∀request,AdapterPublicServerRecord.recordOperations (kdf (n:=n) (Log:=Log) coins setup codec) (.initialKdf request)=
      embed (RegistrationNativePlatformPublicAdapterSealBackend.records coins setup codec (.initialKdf request)) :=by
    intro request
    rw [initial_callback]
    simp only [AdapterPublicServerRecord.recordOperations,kdf,map_eq_bind_pure_comp,Function.comp_def,embed_hom.map_bind,embed_hom.map_pure]
  have ratchetEq :∀request,AdapterPublicServerRecord.recordOperations (kdf (n:=n) (Log:=Log) coins setup codec) (.ratchetKdf request)=
      embed (RegistrationNativePlatformPublicAdapterSealBackend.records coins setup codec (.ratchetKdf request)) :=by
    intro request
    rw [ratchet_callback]
    simp only [AdapterPublicServerRecord.recordOperations,kdf,map_eq_bind_pure_comp,Function.comp_def,embed_hom.map_bind,embed_hom.map_pure]
  rw [first_congr _ (fun query=>embed (n:=n) (RegistrationNativePlatformPublicAdapterSealBackend.records coins setup codec query)) initialEq ratchetEq]
  exact (RegistrationNativePlatformSourceRecord.fromInitialWithHash_map embed_hom
    (RegistrationNativePlatformPublicAdapterSealBackend.records coins setup codec)
    (RegistrationNativePlatformPublicAdapterSealBackend.sealing coins setup codec keyView failure allocation)
    (RegistrationNativePlatformPublicAdapterSealBackend.hash coins setup codec erased)
    (fun request=>StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request)) initial).symm

noncomputable def record
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf) :SourceM (RustM AdapterPublicServerBuildBody.Reply):=
  letI :LocalOperations (RustT SourceM):=localOperations note coins setup codec keyView failure allocation helper sign fallback original
  letI :ChildOperations (RustT SourceM):=children note coins setup codec erased sign writer previous
  letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  do
    let recorded←first note coins setup codec keyView failure allocation helper erased sign fallback original previous writer initial
    modify fun (current :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log))=>((current.1.1,current.1.2++[note (.firstRecord initial recorded)]),current.2)
    AdapterPublicServerRecord.afterRecord self recorded

/-- This source-body decomposition identifies the concrete return at which the analysis observer is inserted. It includes all source failure branches before signing. -/
theorem record_boundary
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf) :
    letI :LocalOperations (RustT SourceM):=localOperations note coins setup codec keyView failure allocation helper sign fallback original
    letI :ChildOperations (RustT SourceM):=children note coins setup codec erased sign writer previous
    letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
    (AdapterPublicServerBuildBody.record (m:=SourceM) self initial).run=
      (do let recorded←first note coins setup codec keyView failure allocation helper erased sign fallback original previous writer initial
          AdapterPublicServerRecord.afterRecord self recorded) :=by
  let :LocalOperations (RustT SourceM):=localOperations note coins setup codec keyView failure allocation helper sign fallback original
  let :ChildOperations (RustT SourceM):=children note coins setup codec erased sign writer previous
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  exact AdapterPublicServerRecord.record (kdf coins setup codec) ⟨fun _=>rfl,fun _=>rfl⟩ self initial

noncomputable def complete
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf) :
    SourceM (AdapterPublicServerBuildTrace.Publication×RustM AdapterPublicServerBuildBody.Reply):=
  letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  do
    let recorded←first note coins setup codec keyView failure allocation helper erased sign fallback original previous writer initial
    modify fun (current :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log))=>((current.1.1,current.1.2++[note (.firstRecord initial recorded)]),current.2)
    let published←RegistrationNativePlatformServerPublication.continueResult recorded
      (RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformCutJournal.source (outgoing note coins sign) fallback)
        (fun signed=>RegistrationNativePlatformCutJournal.liftNative (encoder writer signed)))
    let word←AdapterPublicServerPublication.afterPublication self published
    pure (published,word)

theorem complete_word
    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf) :
    Prod.snd <$>complete note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers self initial=
      record note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers self initial :=by
  let localImpl:=localOperations note coins setup codec keyView failure allocation helper sign fallback original
  let child:=children note coins setup codec erased sign writer previous
  let :LocalOperations (RustT SourceM):=localImpl
  let :ChildOperations (RustT SourceM):=child
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  unfold complete record
  simp only [map_bind,map_pure,bind_pure]
  apply bind_congr
  intro recorded
  apply bind_congr
  intro ignored
  cases recorded with
  | fail error | div=>simp only [RegistrationNativePlatformServerPublication.continueResult,pure_bind,
      AdapterPublicServerRecord.afterRecord,AdapterPublicServerPublication.afterPublication]
  | ok answer=>cases answer with
    | Err refused=>simp only [RegistrationNativePlatformServerPublication.continueResult,pure_bind,
        AdapterPublicServerRecord.afterRecord,AdapterPublicServerPublication.afterPublication]
    | Ok pending=>
      exact (AdapterPublicServerSigningNative.source (outgoing note coins sign) fallback localImpl child
        (fun query=>StateT.lift (writer query)) self pending).symm

omit ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem first_observed    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)

    (initial :registration.ServerInitialKdf) :
    (do let recorded←first note coins setup codec keyView failure allocation helper erased sign fallback original previous writer initial
        modify fun (current :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log))=>
          ((current.1.1,current.1.2++[note (.firstRecord initial recorded)]),current.2)
        pure recorded :SourceM _)=
      RegistrationNativePlatformCutJournal.liftNative
        (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
          (RegistrationNativePlatformPublicAdapterBuildPublication.handler coins setup codec keyView failure allocation helper erased sign writer)
          (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note) (.inl initial)) :=by
  rw [first_normalize]
  apply StateT.ext
  intro before
  change (do let recorded←embed (RegistrationNativePlatformPublicAdapterBuildRecord.firstRecord coins setup codec keyView failure allocation helper erased initial)
             modify fun (current :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log))=>((current.1.1,current.1.2++[note (.firstRecord initial recorded)]),current.2)
             pure recorded :SourceM _).run before=_
  rw [StateT.run_bind]
  simp only [StateT.run_bind,StateT.run_modify,StateT.run_pure,pure_bind]
  simp only [embed,RegistrationNativePlatformCutJournal.liftNative,RegistrationNativePlatformPublicAdapterSourceTrace.recorded,
    StateT.run,bind_pure_comp,Functor.map_map]
  rfl

theorem complete_stage    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf) :
    letI :ContainerOperations (RustT Base):=containers
    complete note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers self initial=
      (do let published←AdapterPublicServerCompletionCut.stage
            (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
              (RegistrationNativePlatformPublicAdapterBuildPublication.handler coins setup codec keyView failure allocation helper erased sign writer)
              (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note) (.inl initial))
            (outgoing note coins sign) fallback (encoder writer)
          let word←StateT.lift (AdapterPublicServerPublication.afterPublication (m:=Base) self published)
          pure (published,word) :SourceM _) :=by
  let :ContainerOperations (RustT Base):=containers
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  have same:=congrArg (fun (action :SourceM (RustM RegistrationServerRecordExecutor.Result))=>do
    let recorded←action
    let published←RegistrationNativePlatformServerPublication.continueResult recorded
      (RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformCutJournal.source (outgoing note coins sign) fallback)
        (fun signed=>RegistrationNativePlatformCutJournal.liftNative (encoder writer signed)))
    let word←StateT.lift (AdapterPublicServerPublication.afterPublication (m:=Base) self published)
    pure (published,word))
    (first_observed note coins setup codec keyView failure allocation helper erased sign fallback original previous writer initial)
  unfold complete
  simp_rw [RegistrationNativePlatformPublicAdapterBuildInstallLift.after_publication
    (S:=RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) containers self]
  simp only [AdapterPublicServerCompletionCut.stage,bind_assoc,pure_bind] at same ⊢
  unfold RegistrationNativePlatformCutJournal.liftNative at same ⊢
  unfold RegistrationNativePlatformCutErasure.liftWorld
  exact same

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem encoder_source (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (signed :registration.SignedResponseView) :
    encoder (n:=n) (KemSK:=KemSK) (Log:=Log) writer signed=
      StateT.lift (RegistrationNativePlatformSourceCompletion.encodeWith writer signed) :=by
  unfold encoder AdapterPublicServerSigningNative.encoder
  change simulateQ (writer.liftTarget Physical)
    (AdapterRegistrationWriterRequestExtraction.encodeResponse (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
      (RegistrationNativeSourceEncoders.responseSyntax signed)).run=_
  rw [simulateQ_liftTarget]
  rfl

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem code_source    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (initial :registration.ServerInitialKdf) :
    RegistrationNativePlatformPublicAdapterBuildStageLog.physical (n:=n) coins setup codec keyView failure allocation helper erased sign writer note initial=
      AdapterPublicServerCompletionCut.native
        (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
          (RegistrationNativePlatformPublicAdapterBuildPublication.handler coins setup codec keyView failure allocation helper erased sign writer)
          (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note) (.inl initial))
        (outgoing (n:=n) note coins sign) (encoder writer) :=by
  unfold RegistrationNativePlatformPublicAdapterBuildStageLog.physical
  rw [RegistrationNativePlatformPublicAdapterBuildStages.interpret]
  unfold AdapterPublicServerCompletionCut.native
  apply bind_congr
  intro recorded
  apply congrArg (RegistrationNativePlatformServerPublication.continueResult recorded)
  funext pending
  apply congrArg (fun encode=>RegistrationNativePlatformServerPublication.program (outgoing note coins sign) encode pending)
  funext signed
  rw [encoder_source]
  apply StateT.ext
  intro before
  simp only [RegistrationNativePlatformPublicAdapterSourceTrace.recorded,
    RegistrationNativePlatformPublicAdapterBuildPublication.handler,
    RegistrationNativePlatformPublicAdapterBuildStages.observation,List.map_nil,List.append_nil,StateT.run]
  change (fun result=>(result.1,(result.2,before.2))) <$>
    (RegistrationNativePlatformSourceCompletion.encodeWith writer signed >>=fun value=>pure (value,before.1))=
    (RegistrationNativePlatformSourceCompletion.encodeWith writer signed >>=fun value=>pure (value,before))
  simp only [map_bind,map_pure]

theorem complete_normalize    (note :Stage→Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest→Physical RegistrationSigningShared.SignReply)
    (original :LocalOperations (RustT Base)) (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (before :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) :
    Prod.map id Prod.fst <$>
      (complete note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers self initial).run before=
      (RegistrationNativePlatformPublicAdapterBuildProgramStages.physicalComplete note coins setup codec keyView failure allocation helper erased sign writer containers self initial).run before.1 :=by
  let :ContainerOperations (RustT Base):=containers
  rw [complete_stage]
  unfold RegistrationNativePlatformPublicAdapterBuildProgramStages.physicalComplete
  rw [code_source note coins setup codec keyView failure allocation helper erased sign writer initial]
  simp only [StateT.run_bind,StateT.run_pure,map_bind]
  have same:=AdapterPublicServerCompletionCut.erasure
    (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildPublication.handler coins setup codec keyView failure allocation helper erased sign writer)
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note) (.inl initial))
    (outgoing note coins sign) fallback (encoder writer) before
  simp only [StateT.run] at same ⊢
  rw [←same,bind_map_left]
  apply bind_congr
  rintro ⟨published,current⟩
  simp only [StateT.lift,map_pure,bind_pure_comp,Functor.map_map,Prod.map,id_eq]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.initial_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.initial_callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.ratchet_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.ratchet_callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.first_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.first_normalize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.record_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.record_boundary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_word

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.first_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.first_observed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_stage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.encoder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.encoder_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.code_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.code_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_normalize
