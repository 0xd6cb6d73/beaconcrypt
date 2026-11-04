-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceWriterNormal
/-! Every concrete Server build source receipt returns normally. The proof derives each source leaf and Core continuation, then reflects normality through the exact same common SDK receipt. Capacity refusals, installation failure, raw source snapshot and platform state are preserved. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSourceBuildNormal (Normal)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {P E I KemSK Reader Response : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
def allocation (reserve : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp) :=
  fun before capacity=>RustM.ok <$>reserve before capacity

theorem complete
    (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view) (failure : primitive.Error)
    (allocate : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (reserveFrame : Nat→StateT P ProbComp (core.result.Result Unit E))
    (reservePackets : Usize→StateT P ProbComp (core.result.Result Unit E))
    (reservePeer : StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) Bool)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Normal (RegistrationNativePlatformExperiment.server (KemSK:=KemSK) (source:=source)
      (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
        reservePeer (RegistrationNativePlatformCompletionSdk.nativePresent coins)
        (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec view failure (allocation allocate)
          (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
          (RegistrationNativePlatformConcreteSource.writer reservePackets)) token application)) := by
  rw [RegistrationNativePlatformExtractedSdkServer.Build.finish_current]
  have built := RegistrationNativePlatformSourceBuildNormal.completeSource coins setup codec
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure (allocation allocate)) erased sign
    (RegistrationNativePlatformConcreteSource.helper reserveFrame) (RegistrationNativePlatformConcreteSource.writer reservePackets)
    (RegistrationNativePlatformSourceSealNormal.sealing coins setup codec view failure converted allocate)
    (RegistrationNativePlatformSourceWriterNormal.write reserveFrame)
    (RegistrationNativePlatformSourceWriterNormal.encode reservePackets) reservePeer token application
  intro before previous result supported
  rw [AdapterPublicServerSourceLens.server_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩ := supported
  obtain ⟨value,normal⟩ := built before.server previous inner called
  subst result
  exact ⟨value,normal⟩

namespace Server
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open AdapterPublicServerBuildBody (Server Reply)
variable {Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT Platform ProbComp
local notation "NativeM" => StateT Native Base
local notation "SourceM" => StateT Cut Base
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
open AdapterPublicServerBuildPrefix (completion finish admitted project application AllocationReply reserveNative)
omit localOps in
theorem normal
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
    (previous : Platform) (result : (AdapterPublicServerBuildTrace.Word×Cut)×Platform) :
    letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure (allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame)
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer (RegistrationNativePlatformConcreteSource.writer reservePackets))
    result∈support (((RegistrationNativePlatformExtractedSdkServer.Build.run coins setup codec keyView failure (allocation allocate)
      (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
      (RegistrationNativePlatformConcreteSource.writer reservePackets) fallback self token data).run before).run previous) →
    ∃word,result.1.1.2=.ok word := by
  let : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure
    (allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame)
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer (RegistrationNativePlatformConcreteSource.writer reservePackets))
  intro supported
  have law:=RegistrationNativePlatformExtractedSdkBuildReachedContains.actual coins setup codec keyView failure
    (allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
    (RegistrationNativePlatformConcreteSource.writer reservePackets) fallback previousLocal previousChildren
    view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
  rw [←RegistrationNativePlatformExtractedSdkServer.Build.finish_current coins setup codec keyView failure
    (allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
    (RegistrationNativePlatformConcreteSource.writer reservePackets)] at law
  have projected : (project self.control result.1,result.2)∈support
      ((project self.control <$>
        (RegistrationNativePlatformExtractedSdkServer.Build.run coins setup codec keyView failure
          (allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
          (RegistrationNativePlatformConcreteSource.writer reservePackets) fallback self token data).run before).run previous) := by
    rw [StateT.run_map,support_map]
    exact ⟨result,supported,rfl⟩
  change (project self.control result.1,result.2)∈support
      ((project self.control <$>
        (AdapterPublicServerBuildTrace.build (completion coins setup codec keyView failure
          (allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
          (RegistrationNativePlatformConcreteSource.writer reservePackets) fallback) self token data).run before).run previous) at projected
  rw [law.2] at projected
  obtain ⟨reply,normal⟩ := complete (source:=mlSource) coins setup codec keyView converted failure allocate erased sign
    reserveFrame reservePackets (admitted <$>StateT.lift allocated) token.registration (application data)
    before.1 previous (project self.control result.1,result.2) projected
  exact RegistrationNativePlatformExtractedSdkServerNormalReflection.build self.control result.1.1.1 result.1.1.2 result.1.2 reply normal
end Server
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal.Server.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal.Server.normal
