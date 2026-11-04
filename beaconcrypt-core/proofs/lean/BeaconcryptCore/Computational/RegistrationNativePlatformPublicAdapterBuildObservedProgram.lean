-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedSource
import BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody
/-! The literal source Builder prefix encloses its internally derived record observer. The executable source result is the actual SDK Word; the private publication receipt is projected before it becomes an output. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitive :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n :Nat} {I KemSK E P Log A :Type} {base :OracleSpec I} {Reader Response :Type}
variable {mlSource :RegistrationNativeMldsa.Source}
local notation "Base"=>StateT P ProbComp
local notation "Physical"=>StateT (Backend n KemSK×List Log) Base
local notation "SourceM"=>StateT (RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) Base

private def lift {S A :Type} (work :StateT S Base A) :StateT (S×List Log) Base A:=fun before=>
  (fun result=>(result.1,(result.2,before.2))) <$>work.run before.1

@[instance_reducible] def locals (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) :LocalOperations (RustT SourceM):=
  {RegistrationNativePlatformPublicAdapterLeaves.localOperations original with
    auth_MldsaIdentity_public_key:=fun identity=>pure (view.mldsa identity).publicKey}

@[instance_reducible] def crypto (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (previous :CryptoOperations (RustT SourceM)) :CryptoOperations (RustT SourceM):=
  {previous with edPublicBytes:=fun key=>pure (view.edPublic key)}

noncomputable def unlogged (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec Physical:=fun query=>
  lift (RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign query)

@[instance_reducible] noncomputable def children (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (previous :ChildOperations (RustT SourceM)) :ChildOperations (RustT SourceM):=
  AdapterPublicServerSigningNative.children (unlogged coins sign) previous (fun query=>StateT.lift (writer query))

noncomputable def receipt
    (note :Stage → Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest → Physical RegistrationSigningShared.SignReply)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :SourceM AdapterPublicServerBuildTrace.Word:=
  letI :LocalOperations (RustT SourceM):=locals view original
  letI :CryptoOperations (RustT SourceM):=crypto view previousCrypto
  letI :ChildOperations (RustT SourceM):=children coins sign writer previous
  letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  AdapterPublicServerBuildTrace.build (RegistrationNativePlatformPublicAdapterBuildObservedSource.complete note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers) self token data

noncomputable def program
    (note :Stage → Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest → Physical RegistrationSigningShared.SignReply)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :SourceM (RustM AdapterPublicServerBuildBody.Reply):=
  letI :LocalOperations (RustT SourceM):=locals view original
  letI :CryptoOperations (RustT SourceM):=crypto view previousCrypto
  letI :ChildOperations (RustT SourceM):=children coins sign writer previous
  letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  (AdapterPublicBuildObservedRequest.run (m:=RustT SourceM)
    (fun current initial=>⟨RegistrationNativePlatformPublicAdapterBuildObservedSource.record note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers current initial⟩)
    self token data).run

theorem receipt_word
    (note :Stage → Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest → Physical RegistrationSigningShared.SignReply)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    Prod.snd <$>receipt note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers self token data=
      program note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers self token data:=by
  let :LocalOperations (RustT SourceM):=locals view original
  let :CryptoOperations (RustT SourceM):=crypto view previousCrypto
  let :ChildOperations (RustT SourceM):=children coins sign writer previous
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  unfold receipt program
  rw [AdapterPublicServerBuildObservedBody.source]
  exact AdapterPublicServerBuildWithRecord.factor _ _
    (RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_word note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers) self token data

noncomputable def handler
    (note :Stage → Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest → Physical RegistrationSigningShared.SignReply)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base)) :QueryImpl RegistrationNativePlatformPublicAdapterBuildProgram.Spec SourceM:=
  letI :LocalOperations (RustT SourceM):=locals view original
  letI :CryptoOperations (RustT SourceM):=crypto view previousCrypto
  letI :ChildOperations (RustT SourceM):=children coins sign writer previous
  letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  RegistrationNativePlatformPublicAdapterBuildProgram.handler (RegistrationNativePlatformPublicAdapterBuildObservedSource.complete note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers)

theorem receipt_code
    (note :Stage → Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest → Physical RegistrationSigningShared.SignReply)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    simulateQ (handler note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers)
      (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)=
      receipt note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers self token data:=by
  let :LocalOperations (RustT SourceM):=locals view original
  let :CryptoOperations (RustT SourceM):=crypto view previousCrypto
  let :ChildOperations (RustT SourceM):=children coins sign writer previous
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  unfold handler receipt
  exact RegistrationNativePlatformPublicAdapterBuildProgram.source _ self token data

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem lift_program {κ :Type} {spec :OracleSpec κ} {S :Type}
    (implementation :QueryImpl spec (StateT S Base)) (work :OracleComp spec A) (before :S×List Log) :
    (simulateQ (fun query=>lift (Log:=Log) (implementation query)) work).run before=
      (lift (simulateQ implementation work)).run before :=by
  rcases before with ⟨current,prior⟩
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation
    (fun query=>lift (Log:=Log) (implementation query)) (fun state=>(state,prior))
    (fun _ _=>rfl) work current
  unfold Prod.map at same
  simpa only [lift,StateT.run,id_eq] using same.symm

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
noncomputable def hash (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationNativeServerPinRecompute.Spec SourceM:=fun request=>
  (fun digest=>RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
    RegistrationNativePlatformCutJournal.hash (unlogged coins sign) request

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem hash_source (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (request :registration.HashRequest) (before :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) :
    Prod.map id Prod.fst <$>(hash coins sign request).run before=
      (lift (Log:=Log) (RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.hash coins sign request)).run before.1 :=by
  unfold hash RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.hash
  rw [StateT.run_map,RegistrationNativePlatformCutJournal.hash_run]
  unfold unlogged lift
  change _=(fun result :RegistrationNativeServerPinRecompute.HashReply×Backend n KemSK=>
    (result.1,(result.2,before.1.2))) <$>
    ((fun digest=>RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
      RegistrationNativePlatformPublicAdapterBuildBackend.outgoing coins sign (.hash request)).run before.1.1
  rw [StateT.run_map]
  simp only [StateT.run,Functor.map_map,Prod.map,id_eq]

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem pin_source
    (coins :QueryImpl unifSpec Base)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (self :beaconcrypt_public_wrapper.server.Server)
    (before :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) :
    letI :LocalOperations (RustT SourceM):=locals view original
    letI :CryptoOperations (RustT SourceM):=crypto view previousCrypto
    letI :ChildOperations (RustT SourceM):=children coins sign writer previous
    Prod.map id Prod.fst <$>
      ((beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT SourceM) self).run).run before=
      (lift (RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.pin coins sign view self)).run before.1 :=by
  let :LocalOperations (RustT SourceM):=locals view original
  let :CryptoOperations (RustT SourceM):=crypto view previousCrypto
  let :ChildOperations (RustT SourceM):=children coins sign writer previous
  rw [AdapterPublicWrapperPin.server_program self _ _ (hash coins sign) rfl rfl (fun _=>rfl)]
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq (hash coins sign)
    (fun request=>lift (Log:=Log) (RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.hash coins sign request))
    Prod.fst (hash_source coins sign)
    (RegistrationNativeServerPinRecompute.program
      ⟨view.edPublic (platform.arcView self.identity).identity_key.public_key,(platform.arcView self.identity).identity_key_kid⟩
      (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey) before
  rw [lift_program] at same
  exact same

theorem query_source    (note :Stage → Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest → Physical RegistrationSigningShared.SignReply)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))

    (query :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (before :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) :
    Prod.map id Prod.fst <$>
      (handler note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers query).run before=
      (RegistrationNativePlatformPublicAdapterBuildProgramStages.physical note coins setup codec keyView failure allocation helper erased sign writer view containers query).run before.1 :=by
  let :LocalOperations (RustT SourceM):=locals view original
  let :CryptoOperations (RustT SourceM):=crypto view previousCrypto
  let :ChildOperations (RustT SourceM):=children coins sign writer previous
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  unfold handler
  cases query with
  | inl self=>exact pin_source coins sign writer view original previousCrypto previous self before
  | inr query=>cases query with
    | inl pair=>
      let work:=(containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
          beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
          hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
          core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
            (core.borrow.Borrow.Blanket U64)) pair.1 pair.2).run
      change Prod.map id Prod.fst <$>(StateT.lift work :SourceM _).run before=
        (lift (StateT.lift work :StateT (Backend n KemSK) Base _)).run before.1
      unfold lift
      simp only [StateT.lift,StateT.run,bind_pure_comp,Functor.map_map,Prod.map,id_eq]
    | inr query=>cases query with
      | inl known=>
        let work:=(containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
            beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
            hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run
        change Prod.map id Prod.fst <$>(StateT.lift work :SourceM _).run before=
          (lift (StateT.lift work :StateT (Backend n KemSK) Base _)).run before.1
        unfold lift
        simp only [StateT.lift,StateT.run,bind_pure_comp,Functor.map_map,Prod.map,id_eq]
      | inr pair=>
        exact RegistrationNativePlatformPublicAdapterBuildObservedSource.complete_normalize
          note coins setup codec keyView failure allocation helper erased sign fallback original previous writer containers pair.1 pair.2 before

theorem program_source    (note :Stage → Log) (coins :QueryImpl unifSpec Base)
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (fallback :registration.MldsaSigningRequest → Physical RegistrationSigningShared.SignReply)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :LocalOperations (RustT Base)) (previousCrypto :CryptoOperations (RustT SourceM))
    (previous :ChildOperations (RustT SourceM))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (containers :ContainerOperations (RustT Base))

    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8))
    (before :RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)) :
    Prod.map id Prod.fst <$>
      (program note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers self token data).run before=
      Prod.map Prod.snd id <$>
        (simulateQ (RegistrationNativePlatformPublicAdapterBuildProgramStages.physical note coins setup codec keyView failure allocation helper erased sign writer view containers)
          (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before.1 :=by
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (handler note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers)
    (RegistrationNativePlatformPublicAdapterBuildProgramStages.physical note coins setup codec keyView failure allocation helper erased sign writer view containers)
    Prod.fst (query_source note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers)
    (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data) before
  rw [receipt_code] at same
  have mapped:=congrArg (fun computation=>Prod.map Prod.snd id <$>computation) same
  have word:=congrArg (fun (action :SourceM (RustM AdapterPublicServerBuildBody.Reply))=>
    Prod.map id Prod.fst <$>action.run before)
    (receipt_word note coins setup codec keyView failure allocation helper erased sign fallback view original previousCrypto previous writer containers self token data).symm
  refine word.trans ?_
  simpa only [StateT.run_map,Functor.map_map,Prod.map,id_eq] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.receipt_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.receipt_word

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.receipt_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.receipt_code

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.hash_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.pin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildObservedProgram.program_source
