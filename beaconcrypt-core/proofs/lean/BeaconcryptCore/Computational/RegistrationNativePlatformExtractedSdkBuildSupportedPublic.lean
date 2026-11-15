-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServerSupported
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! The concrete reached SDK builder obtains its public response directly from the same normal source return. Its continuation retains the actual supported raw receipt and complete source/platform poststate. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildSupportedPublic
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
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(reservePackets : Usize→Base (core.result.Result Unit E))
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
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
      (sourceAfter : Cut) (platformAfter : Platform)
      (_supported : (((publication,.ok (reply,current)),sourceAfter),platformAfter) ∈ support (
      letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
        (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
        (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame)
      letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
        (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
        (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
        (AdapterPublicServerCompletionNative.writer (RegistrationNativePlatformConcreteSource.writer reservePackets))
      (((RegistrationNativePlatformExtractedSdkServer.Build.run coins setup codec keyView failure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign (RegistrationNativePlatformConcreteSource.writer reservePackets) fallback self token data).run before).run previous))),

      AdapterPublicWrapperState.Server view views created credential current
        (project self.control ((publication,.ok (reply,current)),sourceAfter)).2.server →
      Private ((project self.control ((publication,.ok (reply,current)),sourceAfter)).2,platformAfter)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep Private
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (RegistrationNativePlatformSourceBuild.pin coins)
            (admitted <$> StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
            (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign (RegistrationNativePlatformConcreteSource.writer reservePackets))
            token.registration (application data))) (before.1,previous)) := by
  let call := RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Build.step coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
    (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
    (RegistrationNativePlatformConcreteSource.writer reservePackets) fallback previousLocal previousChildren
    view views created credential self before related token data parsed edGetter mlGetter
    allocated reserveOperation footprint containsOperation standard previous Private embed
  refine {
    step := call
    observe := fun returned => AdapterPublicServerPublicationInstall.project (.ok returned)
    normal := ?_
    reply := ?_ }
  · intro packet supported
    exact RegistrationNativePlatformExtractedSdkBuildNormal.Server.normal coins setup codec keyView converted failure
      allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren
      view views created credential self before related token data parsed edGetter mlGetter
      allocated reserveOperation footprint containsOperation standard previous packet supported
  · intro packet _supported returned normal
    change AdapterPublicServerPublicationInstall.project (.ok returned) = (project self.control packet.1).1
    change packet.1.1.2 = .ok returned at normal
    rw [←normal]
    simp only [project,AdapterPublicServerCompletionLifetime.project]
    split <;> rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildSupportedPublic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildSupportedPublic.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildSupportedPublic.step
