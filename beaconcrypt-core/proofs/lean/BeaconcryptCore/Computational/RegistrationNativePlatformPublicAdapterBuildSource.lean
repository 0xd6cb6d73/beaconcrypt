-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildComplete
/-! The entire actual SDK Builder source call executes on an independent physical source interpreter. Its exact source control form and each actual source primitive subtree are consumed in the proof; no native owner state, private hash journal or caller whole-controller law is an executable input. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildTrace (Publication Word)
open RegistrationNativePlatformSdkReification (Backend backend)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitive :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n :Nat} {I KemSK E P :Type} {base :OracleSpec I} {Reader Response :Type}
variable {mlSource :RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "Local"=>RegistrationServerRootCompiler.Local n
local notation "Base"=>StateT P ProbComp
local notation "SourceM"=>StateT (RegistrationNativePlatformCutJournal.State Native) Base
local notation "M"=>StateT (Backend n KemSK) Base
noncomputable def handler (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :ContainerOperations (RustT Base)) :QueryImpl RegistrationNativePlatformPublicAdapterBuildProgram.Spec M
  | .inl self=>RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.pin coins sign view self
  | .inr (.inl (known,identifier))=>StateT.lift
      (original.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) known identifier).run
  | .inr (.inr (.inl known))=>StateT.lift
      (original.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run
  | .inr (.inr (.inr (self,initial)))=>
      RegistrationNativePlatformPublicAdapterBuildComplete.complete coins setup codec keyView failure allocation helper erased sign writer original self initial

noncomputable def program (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (original :ContainerOperations (RustT Base)) (self :beaconcrypt_public_wrapper.server.Server)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) :M Word :=
  simulateQ (handler (n:=n) coins setup codec keyView failure allocation helper erased sign writer view original)
    (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)

noncomputable def nativeHandler (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal :LocalOperations (RustT Base)) (original :ContainerOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previousChildren :ChildOperations (RustT SourceM))
    (fallback :registration.MldsaSigningRequest →StateT Native Base RegistrationSigningShared.SignReply) :QueryImpl RegistrationNativePlatformPublicAdapterBuildProgram.Spec SourceM :=
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  letI :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  letI :LocalOperations (RustT SourceM):=AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  letI :ChildOperations (RustT SourceM):=AdapterPublicServerCompletionSource.children
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  RegistrationNativePlatformPublicAdapterBuildProgram.handler
    (AdapterPublicServerBuildTrace.complete coins setup codec keyView failure allocation helper erased sign writer fallback)

noncomputable def nativeSdk (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal :LocalOperations (RustT Base)) (original :ContainerOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previousChildren :ChildOperations (RustT SourceM))
    (fallback :registration.MldsaSigningRequest →StateT Native Base RegistrationSigningShared.SignReply)
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :SourceM (RustM AdapterPublicServerBuildBody.Reply) :=
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  letI :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  letI :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  letI :LocalOperations (RustT SourceM):=AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  letI :ChildOperations (RustT SourceM):=AdapterPublicServerCompletionSource.children
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  (beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
    (m:=RustT SourceM) self token data).run

theorem query_source (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal :LocalOperations (RustT Base)) (original :ContainerOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previousChildren :ChildOperations (RustT SourceM))
    (fallback :registration.MldsaSigningRequest →StateT Native Base RegistrationSigningShared.SignReply)
    (query :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (before :RegistrationNativePlatformCutJournal.State Native) :
    Prod.map id (fun current=>backend current.1) <$>
      (nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query).run before=
      (handler coins setup codec keyView failure allocation helper erased sign writer view original query).run (backend before.1) := by
  unfold nativeHandler
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  let :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let :LocalOperations (RustT SourceM):=AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let :ChildOperations (RustT SourceM):=AdapterPublicServerCompletionSource.children
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  cases query with
  | inl self=>
    exact RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.pin_source coins sign setup codec view originalLocal previousCrypto
      (AdapterPublicServerRecordNative.children
        (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
        previousChildren coins setup codec erased) writer self before
  | inr query=>cases query with
    | inl pair=>exact RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.contains_source original pair.1 pair.2 before
    | inr query=>cases query with
      | inl known=>exact RegistrationNativePlatformPublicAdapterBuildPrefixPrimitives.reserve_source original known before
      | inr pair=>
        exact RegistrationNativePlatformPublicAdapterBuildComplete.source coins setup codec keyView failure allocation helper erased sign writer
          original fallback pair.1 pair.2 before

theorem source_code (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal :LocalOperations (RustT Base)) (original :ContainerOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previousChildren :ChildOperations (RustT SourceM))
    (fallback :registration.MldsaSigningRequest →StateT Native Base RegistrationSigningShared.SignReply)
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    Prod.snd <$>simulateQ (nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
      (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)=
      nativeSdk coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data := by
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  let :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let :LocalOperations (RustT SourceM):=AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let :ChildOperations (RustT SourceM):=AdapterPublicServerCompletionSource.children
    (fun {A} (work :StateT Local Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  change Prod.snd <$>simulateQ (RegistrationNativePlatformPublicAdapterBuildProgram.handler
    (AdapterPublicServerBuildTrace.complete coins setup codec keyView failure allocation helper erased sign writer fallback))
      (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)=_
  rw [RegistrationNativePlatformPublicAdapterBuildProgram.source]
  exact AdapterPublicServerBuildTrace.source previousLocal previousChildren coins setup codec keyView failure allocation helper erased sign writer fallback self token data

theorem sdk_source (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (sign :registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (originalLocal :LocalOperations (RustT Base)) (original :ContainerOperations (RustT Base))
    (previousCrypto :CryptoOperations (RustT SourceM)) (previousChildren :ChildOperations (RustT SourceM))
    (fallback :registration.MldsaSigningRequest →StateT Native Base RegistrationSigningShared.SignReply)
    (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) (before :RegistrationNativePlatformCutJournal.State Native) :
    Prod.map id (fun current=>backend current.1) <$>
      (nativeSdk coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data).run before=
      (Prod.snd <$>program coins setup codec keyView failure allocation helper erased sign writer view original self token data).run (backend before.1) := by
  rw [←source_code coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data]
  change Prod.map id (fun current=>backend current.1) <$>
    ((fun result=>(result.1.2,result.2)) <$>
      (simulateQ (nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
        (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run before)=_
  have same:=congrArg (fun computation=>(fun result=>(result.1.2,result.2)) <$>computation)
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (fun current=>backend current.1)
      (query_source coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback)
      (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data) before)
  simpa only [program,StateT.run_map,Functor.map_map,Prod.map,id_eq] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource.source_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource.source_code

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource.sdk_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource.sdk_source
