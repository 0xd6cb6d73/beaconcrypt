-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildNative
import BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall
import BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial
import BeaconcryptCore.Refinement.Transport
import BeaconcryptCore.PanicFreedom.Transport
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
/-! The source SDK builder consumes the exact capability it actually received from acceptance. Its entry bookkeeping clears that same native slot before any later rejection, and the same source receipt projects to the literal corrected runtime source builder with the original allocation, publication and mutable installation effects. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildEntry
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

theorem native
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (consumed : peer.ConsumedRegistration) (handle : Nat)
    (tokenRelated : Token token consumed)
    (live : before.1.server.sessions[handle]? = some (some consumed))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (allocated : Base AllocationReply)
    (reserveOperation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views self.known_ids reply)
    (containsOperation : ∀ identifier,
      (containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) self.known_ids identifier).run =
      RustM.ok <$> RegistrationNativePlatformCutErasure.liftWorld
        (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier)))
    (standard : ∀ known publication inserting publicKey,
      peer.begin_peer_insert self.control publication = .ok (.Ok inserting) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey) :
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    project self.control <$>
      ((AdapterPublicServerBuildOwnership.entry handle (AdapterPublicServerBuildTrace.build (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
        self token data)).run before) =
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformSourceSeal.build coins setup codec keyView failure allocation erased
          (admitted <$> allocated) sign helper writer handle (some (application data)))).run before.1 := by
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
  rw [AdapterPublicServerBuildOwnership.entry_run]
  have currentMaterial := AdapterPublicServerBuildOwnership.material_retained view views created credential self before.1 related handle
  have stage := AdapterPublicServerBuildNative.source_joint coins setup codec keyView failure allocation helper erased sign writer fallback previousChildren
    view views created credential self (AdapterPublicServerBuildOwnership.moved handle before.1, before.2) currentMaterial token data parsed
    edGetter mlGetter allocated reserveOperation footprint containsOperation standard
  rw [stage]
  have reserveLift : (admitted <$> StateT.lift allocated : StateT (RegistrationServerFrontendCompiler.State n) Base Bool) =
      StateT.lift (admitted <$> allocated) := by
    apply StateT.ext
    intro server
    simp only [StateT.run_map, StateT.run_lift, map_bind, bind_map_left, map_pure]
  rw [reserveLift]
  change _ = (RegistrationNativePlatformExperiment.server
    (RegistrationNativePlatformCompletionSdk.build (RegistrationNativePlatformSourceBuild.pin coins)
      (StateT.lift (admitted <$> allocated)) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
      (finish coins setup codec keyView failure allocation helper erased sign writer) handle (some (application data)))).run before.1
  simp only [AdapterPublicServerSourceLens.server_run]
  rw [AdapterPublicServerBuildOwnership.build_live _ _ _ _ token consumed before.1 handle tokenRelated live (application data)]
  rfl


omit localOps crypto in
theorem marginal
    (previousLocal : LocalOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)
    [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
      (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
    (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (handle : Nat) :
    letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    Prod.snd <$> AdapterPublicServerBuildOwnership.entry handle (AdapterPublicServerBuildTrace.build (AdapterPublicServerBuildTrace.complete coins setup codec keyView failure allocation helper erased sign writer fallback) self token data) =
      AdapterPublicServerBuildOwnership.entry handle ((beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT SourceM) self token data).run ) := by
  let : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  have actual := AdapterPublicServerBuildTrace.source previousLocal previousChildren coins setup codec keyView failure allocation helper erased sign writer fallback self token data
  exact congrArg (fun work => AdapterPublicServerBuildOwnership.entry handle work) actual

end BeaconcryptCore.Refinement.AdapterPublicServerBuildEntry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildEntry.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildEntry.native
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildEntry.marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildEntry.marginal
