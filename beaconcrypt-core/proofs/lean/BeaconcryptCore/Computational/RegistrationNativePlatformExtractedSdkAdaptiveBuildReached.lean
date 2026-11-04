-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServer
/-! The SDK builder certificate reads its actual source peer map only at states with the proved material relation. The source runner and full raw source poststate are unchanged; the certificate never equates that raw snapshot with its native finalizer. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBuildReached
open BeaconcryptCore.Refinement
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open AdapterPublicServerBuildBody (Server Reply)
variable {n : Nat} {KemSK Platform E I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT Platform ProbComp
local notation "NativeM" => StateT Native Base
local notation "SourceM" => StateT Cut Base
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]

variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
open AdapterPublicServerBuildPrefix (completion finish admitted project application AllocationReply reserveNative)

omit localOps in
noncomputable def step
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (previousLocal.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (allocated : Base AllocationReply)
    (reserveOperation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views self.known_ids reply)
    (containsOperation : ∀ (current : Cut),
      AdapterPublicWrapperState.Server view views created credential self current.1.server →
      ∀ identifier,
      ((containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) self.known_ids identifier).run).run current =
      pure (.ok (views.peer self.known_ids identifier).isSome,
        ({current.1 with server := AdapterPublicServerPresenceNative.charged current.1.server identifier}, current.2)))
    (standard : ∀ known publication inserting publicKey,
      peer.begin_peer_insert self.control publication = .ok (.Ok inserting) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey)
    (previous : Platform) (Private : Native×Platform →Type)
    (embed : ∀(publication : Option AdapterPublicServerBuildTrace.Publication)
      (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
      (sourceAfter : Cut) (platformAfter : Platform),
      AdapterPublicWrapperState.Server view views created credential current
        (project self.control ((publication,.ok (reply,current)),sourceAfter)).2.server →
      Private ((project self.control ((publication,.ok (reply,current)),sourceAfter)).2,platformAfter)) :
    RegistrationNativePlatformExtractedSdkAdaptive.Step Private
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
            (admitted <$> StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
            (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure allocation helper erased sign writer)
            token.registration (application data))) (before.1,previous)) := by
  letI selectedLocal : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  let sampled:=((RegistrationNativePlatformExtractedSdkServer.Build.run coins setup codec keyView failure allocation helper erased sign writer fallback self token data).run before).run previous
  have law:=RegistrationNativePlatformExtractedSdkBuildReachedContains.actual coins setup codec keyView failure allocation helper erased sign writer fallback previousLocal previousChildren
    view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
  rw [←RegistrationNativePlatformExtractedSdkServer.Build.finish_current coins setup codec keyView failure allocation helper erased sign writer] at law
  refine {
    Packet:=(AdapterPublicServerBuildTrace.Word×Cut)×Platform
    sample:=sampled
    sourceType:=Reply
    sourceReply:=fun packet=>packet.1.1.2
    sourceState:=fun packet=>(packet.1.2.1,packet.2)
    sourceCall:=(fun result=>(result.1.1,(result.1.2.1,result.2))) <$>
      ((((beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m:=RustT SourceM) self token data).run).run before).run previous)
    source_exact:=?_
    native:=fun packet=>let result:=project self.control packet.1;(result.1,(result.2,packet.2))
    native_exact:=?_
    store:=?_ }
  · have called:=congrArg (fun work=>((work.run before).run previous)) law.1
    have arranged:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2.1,result.2))) <$>work) called
    simpa only [sampled,RegistrationNativePlatformExtractedSdkServer.Build.run,StateT.run_map,Functor.map_map,Prod.map,id_eq] using arranged
  · have called:=congrArg (fun work=>work.run previous) law.2
    have arranged:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>work) called
    simpa only [sampled,RegistrationNativePlatformExtractedSdkServer.Build.run,RegistrationNativePlatformPackedState.pack,StateT.run_map,Functor.map_map,Prod.map,id_eq] using arranged
  · rintro ⟨⟨⟨publication,word⟩,sourceAfter⟩,platformAfter⟩ supported
    cases word with
    | fail error | div=>exact PUnit.unit
    | ok word=>
      rcases word with ⟨reply,current⟩
      have held:=RegistrationNativePlatformExtractedSdkBuildReachedContains.source_post (localOps:=selectedLocal) coins setup codec keyView failure allocation helper erased sign writer fallback previousChildren
        view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
        publication reply current sourceAfter previous platformAfter supported
      exact embed publication reply current sourceAfter platformAfter held

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBuildReached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBuildReached.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBuildReached.step
