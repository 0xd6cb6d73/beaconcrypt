-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization
/-! Every actual Builder prefix, first-record, hash/sign and writer operation retains the reached shared cache. The same recorded native cut and external platform state remain explicit, including failed source prefixes and later installer refusals. Pure publication finalizers preserve this cache order; no caller frame or security conclusion is assumed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame
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
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {Reader Response : Type}
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


def cache (before :Native):=before.server.world.world.1.primitive.2

omit material platform ed primitive [PublicWrapperPlatform.Allocator] in
theorem outgoing (query :RegistrationSigningShared.Spec.Domain) (before :Native) (previous :P)
    (result :(RegistrationSigningShared.Spec.Range query×Native)×P)
    (supported :result∈support (((AdapterPublicServerCompletionNative.outgoing coins sign query).run before).run previous)) :
    cache before≤cache result.1.2 :=by
  rw [AdapterPublicServerCompletionNative.outgoing,AdapterPublicServerLocalLens.local_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  have actual:=RegistrationNativePlatformHashReceipt.native_support coins _ inner.1 previous inner.2 called
  simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing,StateT.run,support_map] at actual
  obtain ⟨raw,called,same⟩:=actual
  have stateEq:=congrArg Prod.snd same
  change before.server.world.world.1.primitive.2≤ inner.1.2.world.1.primitive.2
  rw [←stateEq]
  cases query with
  | hash request=>
    simp only [RegistrationWorldSigning.outgoing,StateT.run,support_map] at called
    obtain ⟨effect,reached,same⟩:=called
    have worldEq:=congrArg (fun value=>value.2.1) same
    change before.server.world.world.1.primitive.2≤raw.2.1.primitive.2
    rw [←worldEq]
    exact RegistrationWorldCache.effects_cache _ _ _ reached
  | sign request payload digest=>
    simp only [RegistrationWorldSigning.outgoing,StateT.run,support_map] at called
    obtain ⟨effect,reached,same⟩:=called
    have worldEq:=congrArg (fun value=>value.2.1) same
    change before.server.world.world.1.primitive.2≤raw.2.1.primitive.2
    rw [←worldEq]
    exact (RegistrationWorldCache.sampled_cache (sign request) _ effect reached).ge

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem leaf (query :RegistrationNativePlatformPublicAdapterBuildStages.Spec.Domain) (before :Native) (previous :P)
    (result :(RegistrationNativePlatformPublicAdapterBuildStages.Spec.Range query×Native)×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer query).run before).run previous)) :
    cache before≤cache result.1.2 :=by
  cases query with
  | inl initial=>
    change result∈support (((AdapterPublicServerLocalLens.localState
      (RegistrationNativePlatformSourceSealTrace.record coins setup codec keyView failure allocation erased helper initial)).run before).run previous) at supported
    rw [AdapterPublicServerLocalLens.local_run,StateT.run_map,support_map] at supported
    obtain ⟨inner,called,same⟩:=supported
    cases same
    exact (RegistrationNativePlatformSourceFrames.record_frame coins setup codec keyView failure allocation erased helper initial before.server.world previous inner.1 inner.2 called).1
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
      exact le_refl _

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem lifted (query :RegistrationNativePlatformPublicAdapterBuildStages.Spec.Domain) (before :Cut) (previous :P)
    (result :(RegistrationNativePlatformPublicAdapterBuildStages.Spec.Range query×Cut)×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
      (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer) query).run before).run previous)) :
    cache before.1≤cache result.1.2.1 :=by
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


omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem recorded (note :Stage→Log) (query :RegistrationNativePlatformPublicAdapterBuildStages.Spec.Domain)
    (before :Cut×List Log) (previous :P)
    (result :(RegistrationNativePlatformPublicAdapterBuildStages.Spec.Range query×(Cut×List Log))×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note) query).run before).run previous)) :
    cache before.1.1≤cache result.1.2.1.1 :=by
  change result∈support (((fun inner=>(inner.1,(inner.2,before.2++
    (RegistrationNativePlatformPublicAdapterBuildStages.observation query inner.1).map note))) <$>
    (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
      (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer) query).run before.1).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact lifted coins setup codec keyView failure allocation helper erased sign writer query before.1 previous inner called

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem program (note :Stage→Log) (work :OracleComp RegistrationNativePlatformPublicAdapterBuildStages.Spec A)
    (before :Cut×List Log) (previous :P) (result :(A×(Cut×List Log))×P)
    (supported :result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note)) work).run before).run previous)) :
    cache before.1.1≤cache result.1.2.1.1 :=by
  exact RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ (fun current=>cache before.1.1≤cache current.1.1)
    (fun query current external held output called=>held.trans (recorded coins setup codec keyView failure allocation helper erased sign writer note query current external output called))
    work before previous (le_refl _) result supported

theorem complete (note :Stage→Log) (original :ContainerOperations (RustT Base))
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (before :Cut×List Log) (previous :P)
    (result :((Publication×RustM AdapterPublicServerBuildBody.Reply)×(Cut×List Log))×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.nativeComplete
      note coins setup codec keyView failure allocation helper erased sign writer original self initial).run before).run previous)) :
    cache before.1.1≤cache result.1.2.1.1 :=by
  let :ContainerOperations (RustT Base):=original
  change result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded
      (RegistrationNativePlatformPublicAdapterBuildStageCut.lifted
        (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec keyView failure allocation helper erased sign writer))
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
      (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run before >>=fun published=>do
        let word←AdapterPublicServerPublication.afterPublication (m:=Base) self published.1
        pure ((published.1,word),published.2)).run previous) at supported
  simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨published,called,word,_installed,same⟩:=supported
  cases same
  exact program coins setup codec keyView failure allocation helper erased sign writer note _ before previous published called


omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem hash_global (request :registration.HashRequest) (before :Native) (previous :P)
    (result :(RegistrationNativeServerPinRecompute.HashReply×Native)×P)
    (supported :result∈support (((AdapterPublicServerPinGlobal.hash coins request).run before).run previous)) :
    cache before≤cache result.1.2 :=by
  rw [AdapterPublicServerPinGlobal.hash,AdapterPublicServerWorldLens.world_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  have actual:=RegistrationNativePlatformHashReceipt.native_support coins
    ((RegistrationNativeServerPinRecompute.nativeHash request).run before.server.world.world.1) inner.1 previous inner.2 called
  simp only [RegistrationNativeServerPinRecompute.nativeHash,bind_pure_comp,StateT.run_map,support_map] at actual
  obtain ⟨hashed,reached,same⟩:=actual
  change before.server.world.world.1.primitive.2≤ inner.1.2.primitive.2
  rw [←congrArg (fun value=>value.2.primitive.2) same]
  exact RegistrationWorldCache.effects_cache _ _ _ reached

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem hash (request :registration.HashRequest) (before :Cut) (previous :P)
    (result :(RegistrationNativeServerPinRecompute.HashReply×Cut)×P)
    (supported :result∈support (((AdapterPublicServerCutPin.hash coins sign request).run before).run previous)) :
    cache before.1≤cache result.1.2.1 :=by
  have law:=congrArg (fun work=>work.run previous) (AdapterPublicServerCutPin.hash_erasure coins sign request before)
  rw [StateT.run_map] at law
  have mapped :((result.1.1,result.1.2.1),result.2)∈support
      (((AdapterPublicServerPinGlobal.hash coins request).run before.1).run previous) :=by
    rw [←law,support_map]
    exact ⟨result,supported,rfl⟩
  exact hash_global coins request before.1 previous _ mapped

variable (originalLocal :LocalOperations (RustT (StateT P ProbComp))) (original :ContainerOperations (RustT (StateT P ProbComp)))
variable (previousCrypto :CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (previousChildren :ChildOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (fallback :registration.MldsaSigningRequest→StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp) RegistrationSigningShared.SignReply)

theorem prefix_native (query :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain) (allowed :RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix query)
    (before :Cut) (previous :P)
    (result :(RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range query×Cut)×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query).run before).run previous)) :
    cache before.1≤cache result.1.2.1 :=by
  unfold RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler at supported
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  let :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let :LocalOperations (RustT SourceM):=AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work :StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let :ChildOperations (RustT SourceM):=AdapterPublicServerCompletionSource.children
    (fun {A} (work :StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  cases query with
  | inl self=>
    change result∈support ((((beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT SourceM) self).run).run before).run previous) at supported
    rw [AdapterPublicWrapperPin.server_program self _ _ (AdapterPublicServerCutPin.hash coins sign) rfl rfl (fun _=>rfl)] at supported
    exact RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ (fun current=>cache before.1≤cache current.1)
      (fun request current external held output called=>held.trans (hash coins sign request current external output called))
      _ before previous (le_refl _) result supported
  | inr query=>cases query with
    | inl pair=>
      let requested :Base (RustM Bool):=(original.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
        (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) pair.1 pair.2).run
      change result∈support (((do
        let output←StateT.lift requested
        modify fun current :Cut=>({current.1 with server:=AdapterPublicServerPresenceNative.charged current.1.server 0#u64},current.2)
        pure output :SourceM _).run before).run previous) at supported
      simp only [StateT.run_bind,StateT.run_lift,bind_pure_comp,StateT.run_map,StateT.run_modify,map_pure,Functor.map_map,support_map] at supported
      obtain ⟨inner,_called,same⟩:=supported
      cases same
      exact le_refl _
    | inr query=>cases query with
      | inl known=>
        change result∈support (((StateT.lift (original.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
          beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
          hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run :SourceM _).run before).run previous) at supported
        simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at supported
        obtain ⟨inner,_called,same⟩:=supported
        cases same
        exact le_refl _
      | inr pair=>exact allowed.elim

theorem prefix_recorded (note :Stage→Log) (request :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (allowed :RegistrationNativePlatformPublicAdapterBuildReceiptFrame.Prefix request)
    (before :Cut×List Log) (previous :P)
    (result :((RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range request×(Cut×List Log))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before).run previous)) :
    cache before.1.1≤cache result.1.2.1.1 :=by
  have same :RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request =
      (fun (before :Cut×List Log)=> (fun inner=>(inner.1,(inner.2,before.2))) <$>
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
  exact prefix_native coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request allowed before.1 previous inner called

theorem query (note :Stage→Log) (request :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain)
    (before :Cut×List Log) (previous :P)
    (result :((RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range request×(Cut×List Log))×P))
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback request).run before).run previous)) :
    cache before.1.1≤cache result.1.2.1.1 :=by
  cases request with
  | inl self=>exact prefix_recorded coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback note (.inl self) True.intro before previous result supported
  | inr request=>cases request with
    | inl pair=>exact prefix_recorded coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback note (.inr (.inl pair)) True.intro before previous result supported
    | inr request=>cases request with
      | inl known=>exact prefix_recorded coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback note (.inr (.inr (.inl known))) True.intro before previous result supported
      | inr pair=>exact complete coins setup codec keyView failure allocation helper erased sign writer note original pair.1 pair.2 before previous result supported

theorem whole_program (note :Stage→Log) (work :OracleComp RegistrationNativePlatformPublicAdapterBuildProgram.Spec A)
    (before :Cut×List Log) (previous :P)
    (result :(A×(Cut×List Log))×P)
    (supported :result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterBuildProgramStages.native
      note coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback) work).run before).run previous)) :
    cache before.1.1≤cache result.1.2.1.1 :=by
  exact RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ (fun current=>cache before.1.1≤cache current.1.1)
    (fun request current external held output called=>held.trans (query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback note request current external output called))
    work before previous (le_refl _) result supported


omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem world_pure (value :A) :
    RegistrationNativePlatformServerSdk.world (pure value :StateT (RegistrationServerRootCompiler.Local n) Base A)=
      (pure value :StateT (RegistrationServerFrontendCompiler.State n) Base A) :=by
  apply StateT.ext
  intro before
  change (fun result=>(result.1,{before with world:=result.2})) <$>pure (value,before.world)=pure (value,before)
  rw [map_pure]

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem capability (pending :peer.PeerInsert (alloc.vec.Vec U8)) (before :RegistrationServerFrontendCompiler.State n)
    (result :Bool×RegistrationServerFrontendCompiler.State n)
    (supported :result∈support ((AdapterPublicServerInstallNative.capability pending).run before)) :
    before.world.world.1.primitive.2≤result.2.world.world.1.primitive.2 :=by
  simp only [AdapterPublicServerInstallNative.capability,RegistrationNativePlatformServerSdk.world,
    RegistrationWorldServerCompletion.capability,StateT.run,Functor.map_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact RegistrationWorldCache.effects_cache _ _ inner called

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem commit (finished :RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)))
    (before :RegistrationServerFrontendCompiler.State n) (previous :P)
    (result :(RustM (Option (U64×alloc.vec.Vec U8))×RegistrationServerFrontendCompiler.State n)×P)
    (supported :result∈support (((RegistrationNativePlatformServerSdk.commit (m:=StateT P ProbComp) finished).run before).run previous)) :
    before.world.world.1.primitive.2≤result.1.2.world.world.1.primitive.2 :=by
  cases finished with
  | fail error=>
    change result∈support (pure ((RustM.fail error,before),previous)) at supported
    simp only [support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact le_refl _
  | div=>
    change result∈support (pure ((RustM.div,before),previous)) at supported
    simp only [support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact le_refl _
  | ok finished=>cases finished with
    | Err rejected=>
      change result∈support (pure ((RustM.ok none,{before with control:=rejected}),previous)) at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _
    | Ok published=>
      change result∈support (pure ((RustM.ok (some (published.key_id,published.encoded)),{before with control:=published.control}),previous)) at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem native_tail (coins :QueryImpl unifSpec (StateT P ProbComp)) (control :pqxdh.ServerState)
    (published :RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before :RegistrationServerFrontendCompiler.State n) (previous :P)
    (result :(RustM (Option (U64×alloc.vec.Vec U8))×RegistrationServerFrontendCompiler.State n)×P)
    (supported :result∈support (((AdapterPublicServerPublicationInstall.native coins control published).run before).run previous)) :
    before.world.world.1.primitive.2≤result.1.2.world.world.1.primitive.2 :=by
  cases published with
  | fail error | div=>
    simp only [AdapterPublicServerPublicationInstall.native,RegistrationNativePlatformServerCompletion.continueResult,
      world_pure,pure_bind] at supported
    exact commit _ before previous result supported
  | ok published=>cases published with
    | Err rejected=>
      simp only [AdapterPublicServerPublicationInstall.native,RegistrationNativePlatformServerCompletion.continueResult,
        world_pure,pure_bind] at supported
      exact commit _ before previous result supported
    | Ok published=>
      obtain ⟨begun,began,_retained⟩:=PeerOwnership.peer_insert_begin_retains control published
      cases begun with
      | Err rejected=>
        simp only [AdapterPublicServerPublicationInstall.native,RegistrationNativePlatformServerCompletion.continueResult,
          RegistrationNativePlatformServerCompletion.installWith,began,world_pure,pure_bind] at supported
        exact commit _ before previous result supported
      | Ok pending=>
        rw [AdapterPublicServerPublicationInstall.native_insert coins control published pending began] at supported
        simp only [StateT.run_bind,mem_support_bind_iff] at supported
        obtain ⟨middle,called,following⟩:=supported
        have original:=RegistrationNativePlatformHashReceipt.native_support coins _ middle.1 previous middle.2 called
        exact (capability pending before middle.1 original).trans (commit _ middle.1.2 middle.2 result following)

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem tail (control :pqxdh.ServerState)
    (published :RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) (before :RegistrationServerFrontendCompiler.State n) :
    before.world.world.1.primitive.2≤(AdapterPublicServerTailCanonical.result control published before).2.world.world.1.primitive.2 :=by
  let sampler :QueryImpl unifSpec (StateT Unit ProbComp):=fun query=>StateT.lift (unifSpec.query query)
  have supported : (AdapterPublicServerTailCanonical.result control published before,())∈support
      (((AdapterPublicServerPublicationInstall.native sampler control published).run before).run ()) :=by
    rw [AdapterPublicServerTailCanonical.native_run,StateT.run_pure,support_pure,Set.mem_singleton_iff]
  exact native_tail sampler control published before () _ supported

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem completion_project (control :pqxdh.ServerState)
    (result :((RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))×RustM AdapterPublicServerBuildBody.Reply)×Cut)) :
    result.2.1.server.world.world.1.primitive.2≤(AdapterPublicServerCompletionLifetime.project control result).2.server.world.world.1.primitive.2 :=
  tail control result.1.1 result.2.1.server

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem build_project (control :pqxdh.ServerState) (result :AdapterPublicServerBuildTrace.Word×Cut) :
    result.2.1.server.world.world.1.primitive.2≤(AdapterPublicServerBuildPrefix.project control result).2.server.world.world.1.primitive.2 :=by
  unfold AdapterPublicServerBuildPrefix.project
  cases result.1.1 with
  | none=>exact le_refl _
  | some published=>exact completion_project control ((published,result.1.2),result.2)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.leaf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.lifted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.recorded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.prefix_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.prefix_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.prefix_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.prefix_recorded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.whole_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.whole_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.native_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.native_tail

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.tail

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.completion_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.completion_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.build_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCacheFrame.build_project
