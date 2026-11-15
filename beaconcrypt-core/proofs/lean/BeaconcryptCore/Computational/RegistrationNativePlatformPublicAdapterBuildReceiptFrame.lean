-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta
/-! The actual non-completion Builder prefix does not append a signing receipt. This is derived from its real source pin/hash and container leaves, including every failed return. The publication bookkeeping projections preserve the raw receipt list independently of their result. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK E P A :Type} {base :OracleSpec I} {Reader Response :Type} {mlSource :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitive :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut"=>RegistrationNativePlatformCutJournal.State Native
local notation "Base"=>StateT P ProbComp
local notation "M"=>StateT Cut Base

def history (before :Cut):=before.1.server.world.world.2

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem world (work :StateT (PqxdhRecordLiftWorld.State n) Base A) (before :Native) (previous :P)
    (result :(A×Native)×P) (supported :result∈support (((AdapterPublicServerWorldLens.world work).run before).run previous)) :
    result.1.2.server.world.world.2=before.server.world.world.2 :=by
  simp only [AdapterPublicServerWorldLens.world_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,same⟩:=supported
  cases same
  rfl

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem hash (coins :QueryImpl unifSpec (StateT P ProbComp))
    (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply) (request :registration.HashRequest)
    (before :Cut) (previous :P) (result :(RegistrationNativeServerPinRecompute.HashReply×Cut)×P)
    (supported :result∈support (((AdapterPublicServerCutPin.hash coins sign request).run before).run previous)) :
    history result.1.2=history before :=by
  have law:=congrArg (fun work=>work.run previous) (AdapterPublicServerCutPin.hash_erasure coins sign request before)
  rw [StateT.run_map] at law
  have mapped :((result.1.1,result.1.2.1),result.2)∈support
      (((AdapterPublicServerPinGlobal.hash coins request).run before.1).run previous) :=by
    rw [←law,support_map]
    exact ⟨result,supported,rfl⟩
  exact world _ before.1 previous _ mapped

def Prefix :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain→Prop
  | .inr (.inr (.inr _))=>False
  | _=>True

variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
variable (keyView :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
variable (allocation :RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp)) (erased :commitment.CommitmentTranscript)
variable (sign :registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
variable (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
variable (originalLocal :LocalOperations (RustT (StateT P ProbComp))) (original :ContainerOperations (RustT (StateT P ProbComp)))
variable (previousCrypto :CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (previousChildren :ChildOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (fallback :registration.MldsaSigningRequest→StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp) RegistrationSigningShared.SignReply)

theorem query (query :RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Domain) (allowed :Prefix query)
    (before :Cut) (previous :P)
    (result :(RegistrationNativePlatformPublicAdapterBuildProgram.Spec.Range query×Cut)×P)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback query).run before).run previous)) :
    history result.1.2=history before :=by
  unfold RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler at supported
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  let :ContainerOperations (RustT M):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) original
  let :CryptoOperations (RustT M):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let :LocalOperations (RustT M):=AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work :StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let :ChildOperations (RustT M):=AdapterPublicServerCompletionSource.children
    (fun {A} (work :StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  cases query with
  | inl operation=>cases operation with
    | inl self=>
      change result∈support ((((beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT M) self).run).run before).run previous) at supported
      rw [AdapterPublicWrapperPin.server_program self _ _ rfl rfl] at supported
      simp only [StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      rfl
    | inr request=>
      change result ∈ support (((AdapterPublicServerCutPin.hash coins sign request).run before).run previous) at supported
      exact hash coins sign request before previous result supported
  | inr query=>cases query with
    | inl pair=>
      let requested :Base (RustM Bool):=(original.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
        (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) pair.1 pair.2).run
      change result∈support (((do
        let output←StateT.lift requested
        modify fun current :Cut=>({current.1 with server:=AdapterPublicServerPresenceNative.charged current.1.server 0#u64},current.2)
        pure output :M _).run before).run previous) at supported
      simp only [StateT.run_bind,StateT.run_lift,bind_pure_comp,StateT.run_map,StateT.run_modify,map_pure,Functor.map_map,support_map] at supported
      obtain ⟨inner,_called,same⟩:=supported
      cases same
      rfl
    | inr query=>cases query with
      | inl known=>
        change result∈support (((StateT.lift (original.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
          beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
          hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run :M _).run before).run previous) at supported
        simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at supported
        obtain ⟨inner,_called,same⟩:=supported
        cases same
        rfl
      | inr pair=>exact allowed.elim

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
    result.2.world.world.2=before.world.world.2 :=by
  simp only [AdapterPublicServerInstallNative.capability,RegistrationNativePlatformServerSdk.world,
    RegistrationWorldServerCompletion.capability,PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,StateT.run,Functor.map_map,support_map] at supported
  obtain ⟨inner,_called,same⟩:=supported
  cases same
  rfl

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem commit (finished :RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)))
    (before :RegistrationServerFrontendCompiler.State n) (previous :P)
    (result :(RustM (Option (U64×alloc.vec.Vec U8))×RegistrationServerFrontendCompiler.State n)×P)
    (supported :result∈support (((RegistrationNativePlatformServerSdk.commit (m:=StateT P ProbComp) finished).run before).run previous)) :
    result.1.2.world.world.2=before.world.world.2 :=by
  cases finished with
  | fail error=>
    change result∈support (pure ((RustM.fail error,before),previous)) at supported
    simp only [support_pure,Set.mem_singleton_iff] at supported
    cases supported
    rfl
  | div=>
    change result∈support (pure ((RustM.div,before),previous)) at supported
    simp only [support_pure,Set.mem_singleton_iff] at supported
    cases supported
    rfl
  | ok finished=>cases finished with
    | Err rejected=>
      change result∈support (pure ((RustM.ok none,{before with control:=rejected}),previous)) at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      cases supported
      rfl
    | Ok published=>
      change result∈support (pure ((RustM.ok (some (published.key_id,published.encoded)),{before with control:=published.control}),previous)) at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      cases supported
      rfl

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem native_tail (coins :QueryImpl unifSpec (StateT P ProbComp)) (control :pqxdh.ServerState)
    (published :RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before :RegistrationServerFrontendCompiler.State n) (previous :P)
    (result :(RustM (Option (U64×alloc.vec.Vec U8))×RegistrationServerFrontendCompiler.State n)×P)
    (supported :result∈support (((AdapterPublicServerPublicationInstall.native coins control published).run before).run previous)) :
    result.1.2.world.world.2=before.world.world.2 :=by
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
        exact (commit _ middle.1.2 middle.2 result following).trans (capability pending before middle.1 original)

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem tail (control :pqxdh.ServerState)
    (published :RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) (before :RegistrationServerFrontendCompiler.State n) :
    (AdapterPublicServerTailCanonical.result control published before).2.world.world.2=before.world.world.2 :=by
  let sampler :QueryImpl unifSpec (StateT Unit ProbComp):=fun query=>StateT.lift (unifSpec.query query)
  have supported : (AdapterPublicServerTailCanonical.result control published before,())∈support
      (((AdapterPublicServerPublicationInstall.native sampler control published).run before).run ()) :=by
    rw [AdapterPublicServerTailCanonical.native_run,StateT.run_pure,support_pure,Set.mem_singleton_iff]
  exact native_tail sampler control published before () _ supported

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem completion_project (control :pqxdh.ServerState)
    (result :((RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))×RustM AdapterPublicServerBuildBody.Reply)×Cut)) :
    (AdapterPublicServerCompletionLifetime.project control result).2.server.world.world.2=result.2.1.server.world.world.2 :=
  tail control result.1.1 result.2.1.server

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem build_project (control :pqxdh.ServerState) (result :AdapterPublicServerBuildTrace.Word×Cut) :
    (AdapterPublicServerBuildPrefix.project control result).2.server.world.world.2=result.2.1.server.world.world.2 :=by
  unfold AdapterPublicServerBuildPrefix.project
  cases result.1.1 with
  | none=>rfl
  | some published=>exact completion_project control _

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.hash
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.native_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.native_tail
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.tail
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.completion_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.completion_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.build_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildReceiptFrame.build_project
