-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
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
set_option backward.isDefEq.respectTransparency false
/-! The actual SDK map-membership leaf is required only at the reached Server material representation. Its reply is the literal source-container readback, with the same analysis-only administrative charge and unchanged platform state. No statement is imposed on unrelated native states. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains
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

open AdapterPublicServerBuildPrefix (completion finish admitted project application AllocationReply reserveNative lookupNative lookup_global afterPin reserved)

omit primitive containers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
noncomputable def readback (views : Views) (known : PeerMap) (identifier : U64) : RustT SourceM Bool :=
  ⟨fun before => pure (.ok (views.peer known identifier).isSome,
    ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2))⟩

omit primitive containers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem readback_source (coins : QueryImpl unifSpec Base)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut)
    (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (identifier : U64) :
    (readback (n:=n) (KemSK:=KemSK) (mlSource:=mlSource) (Platform:=Platform) views self.known_ids identifier).run.run before =
    (RustM.ok <$> RegistrationNativePlatformCutErasure.liftWorld
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier))).run before := by
  have present := AdapterPublicServerPresenceNative.source coins view views created credential self before.1.server related identifier
  rw [StateT.run_map]
  change pure _ = (fun result : Bool × Cut => (RustM.ok result.1, result.2)) <$>
    ((fun result : Bool × Native => (result.1, (result.2, before.2))) <$>
    (RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier)).run before.1)
  rw [AdapterPublicServerSourceLens.server_run, present, map_pure, map_pure, map_pure]

theorem lookup
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    [children : ChildOperations (RustT SourceM)]
    (hashOperation : ∀ request, (children.executeHash request).run = AdapterPublicServerCutPin.hash coins sign request)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (pin : session.ServerAuthenticationPin) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (plaintext : Slice U8) (pending : peer.CompletionLookup)
    (began : peer.begin_completion_lookup self.control pin token.registration plaintext = .ok (.Ok pending))
    (parsed : AdapterPublicServerToken.ParsedToken token)
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
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey) :
    project self.control <$>
      ((AdapterPublicServerBuildTrace.lookup (m := SourceM) (completion coins setup codec keyView failure allocation helper erased sign writer fallback) self pending plaintext).run before) =
      (lookupNative coins (reserveNative allocated) (finish coins setup codec keyView failure allocation helper erased sign writer) self.control pending plaintext).run before.1 := by
  have fields := AdapterPublicServerBuildReceipt.lookup_fields self.control pin token.registration plaintext pending began
  have wrapped : ∀ length identifier,
      (beaconcrypt_public_request.server.registration_response_len (m := RustT SourceM) length identifier).run =
        pure (transport.registration_response_len length identifier) := fun _ _ => rfl
  unfold AdapterPublicServerBuildTrace.lookup AdapterPublicServerBuildTrace.invoke lookupNative
  simp only [RustT.run_liftRust, pure_bind]
  cases requested : pending.request with
  | fail error | div => simp only [StateT.run_pure, map_pure, project, AdapterPublicServerPublicationInstall.project]
  | ok identifier =>
    simp only []
    have size : CoreModels.core.slice.Slice.len plaintext = .ok plaintext.len := rfl
    rw [size]
    simp only []
    rw [wrapped]
    simp only [pure_bind]
    obtain ⟨capacity, sized⟩ := BeaconcryptCore.PanicFreedom.Transport.registration_response_len_total plaintext.len identifier
    rw [sized]
    cases capacity with
    | none => simp only [RegistrationServerSdkSource.preflight, sized, StateT.run_pure, map_pure, project,
        AdapterPublicServerPublicationInstall.project, AdapterPublicServerPublicationInstall.output, Bool.false_eq_true, ↓reduceIte]
    | some capacity =>
      simp only [RegistrationServerSdkSource.preflight, sized, ↓reduceIte]
      simp only [StateT.run_bind, map_bind]
      rw [containsOperation before related identifier]
      have present := AdapterPublicServerPresenceNative.source coins view views created credential self before.1.server related identifier
      rw [AdapterPublicServerSourceLens.server_run, present, map_pure]
      simp only [pure_bind]
      unfold AdapterPublicServerBuildTrace.checked
      cases resumed : pending.resume (views.peer self.known_ids identifier).isSome with
      | fail error =>
        change project self.control <$> (pure ((none, .fail error),
          ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2)) : Base _) =
          pure (.fail error, {before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier})
        simp only [map_pure, project, AdapterPublicServerPublicationInstall.project]
      | div =>
        change project self.control <$> (pure ((none, .div),
          ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2)) : Base _) =
          pure (.div, {before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier})
        simp only [map_pure, project, AdapterPublicServerPublicationInstall.project]
      | ok result => cases result with
        | Err old =>
          change project self.control <$> (pure ((none, .ok (.None, self)),
            ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2)) : Base _) =
            pure (.ok none, {before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier})
          simp only [map_pure, project, AdapterPublicServerPublicationInstall.project, AdapterPublicServerPublicationInstall.output]
        | Ok pendingAd =>
          have selected : registration.begin_server_completion self.control pin
              (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
              token.registration.agreement plaintext = .ok (.Ok pendingAd) := by
            cases occupied : (views.peer self.known_ids identifier).isSome <;>
              simpa only [occupied, PeerOwnership.completion_lookup_resume, fields.1, fields.2.1,
                fields.2.2.1, fields.2.2.2] using resumed
          have previous := RegistrationServerCompletionSnapshot.ad_selection self.control pin
            (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
            token.registration.agreement plaintext (.Ok pendingAd) selected
          have origin := RegistrationAd.server_ad_origin self.control pin
            (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
            token.registration.agreement plaintext pendingAd selected
          have parsedPending : AdapterPublicServerToken.ParsedBinding pendingAd.binding := by
            rw [origin.2.1]
            exact parsed
          have currentMaterial := AdapterPublicServerPresenceNative.material_related view views created credential self before.1.server related identifier
          exact AdapterPublicServerBuildPrefix.hashed coins setup codec keyView failure allocation helper erased sign writer fallback hashOperation
            view views created credential self
            ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2)
            currentMaterial pendingAd previous parsedPending allocated reserveOperation footprint standard

theorem after_pin
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    [children : ChildOperations (RustT SourceM)]
    (hashOperation : ∀ request, (children.executeHash request).run = AdapterPublicServerCutPin.hash coins sign request)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (plaintext : Slice U8)
    (pinned : RustM (core.option.Option session.ServerAuthenticationPin))
    (parsed : AdapterPublicServerToken.ParsedToken token)
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
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey) :
    project self.control <$>
      ((afterPin (completion coins setup codec keyView failure allocation helper erased sign writer fallback) self token plaintext pinned).run before) =
    (RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformCompletionSdk.afterPin
        (RegistrationNativePlatformCompletionSdk.nativeAdHash coins)
        (admitted <$> StateT.lift allocated)
        (RegistrationNativePlatformCompletionSdk.nativePresent coins)
        (finish coins setup codec keyView failure allocation helper erased sign writer)
        self.control token.registration plaintext pinned)).run before.1 := by
  unfold afterPin RegistrationNativePlatformCompletionSdk.afterPin
  cases pinned with
  | fail error | div => simp only [AdapterPublicServerSourceLens.server_pure, StateT.run_pure, map_pure, project,
      AdapterPublicServerPublicationInstall.project]
  | ok optional => cases optional with
    | none => simp only [AdapterPublicServerSourceLens.server_pure, StateT.run_pure, map_pure, project,
        AdapterPublicServerPublicationInstall.project, AdapterPublicServerPublicationInstall.output]
    | some pin =>
      simp only []
      unfold AdapterPublicServerBuildTrace.checked
      cases began : peer.begin_completion_lookup self.control pin token.registration plaintext with
      | fail error | div => simp only [AdapterPublicServerSourceLens.server_pure, StateT.run_pure, map_pure, project,
          AdapterPublicServerPublicationInstall.project]
      | ok result => cases result with
        | Err old => simp only [AdapterPublicServerSourceLens.server_pure, StateT.run_pure, map_pure, project,
            AdapterPublicServerPublicationInstall.project, AdapterPublicServerPublicationInstall.output]
        | Ok pending =>
          rw [lookup coins setup codec keyView failure allocation helper erased sign writer fallback hashOperation
            view views created credential self before related pin token plaintext pending began parsed
            allocated reserveOperation footprint containsOperation standard, lookup_global]
          rfl

variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]

theorem source_joint
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
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
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
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey) :
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    project self.control <$>
      ((AdapterPublicServerBuildTrace.build (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
        self token data).run before) =
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformCompletionSdk.complete
          (RegistrationNativePlatformCompletionSdk.nativeAdHash coins)
          (RegistrationNativePlatformSourceBuild.pin coins)
          (admitted <$> StateT.lift allocated)
          (RegistrationNativePlatformCompletionSdk.nativePresent coins)
          (finish coins setup codec keyView failure allocation helper erased sign writer)
          token.registration (application data))).run before.1 := by
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
  have pinErasure := AdapterPublicServerCutPin.source coins view views created credential
    (AdapterPublicServerRecordNative.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      previousChildren coins setup codec erased)
    (AdapterPublicServerCompletionNative.writer writer) self before related edGetter mlGetter
  rw [AdapterPublicServerBuildPrefix.normalized, StateT.run_bind, map_bind,
    AdapterPublicServerBuildPrefix.complete_global_run, ← related.control, ← pinErasure, bind_map_left]
  apply StateT.ext
  intro external
  simp only [StateT.run_bind, StateT.run_map]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨pinned, current⟩, between⟩ supported
  have projectedSupport : ((pinned, current.1), between) ∈ support
      ((Prod.map id Prod.fst <$>
        (((beaconcrypt_public_request.server.Server.authentication_pin (m := RustT SourceM) self).run).run before)).run external) := by
    rw [StateT.run_map, support_map]
    exact ⟨((pinned, current), between), supported, rfl⟩
  rw [pinErasure] at projectedSupport
  have currentMaterial := AdapterPublicServerBuildPrefix.pin_material coins view views created credential self before.1 current.1
    related pinned external between projectedSupport
  simpa only [StateT.run_map, Prod.map, id_eq] using congrArg (fun work => work.run between)
    (after_pin coins setup codec keyView failure allocation helper erased sign writer fallback (fun _ => rfl)
      view views created credential self current currentMaterial token (application data) pinned parsed
      allocated reserveOperation footprint containsOperation standard)

omit localOps in
theorem actual
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
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey) :
    letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    (Prod.snd <$> AdapterPublicServerBuildTrace.build (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
      self token data =
      (beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT SourceM) self token data).run) ∧
    project self.control <$>
      ((AdapterPublicServerBuildTrace.build (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
        self token data).run before) =
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformCompletionSdk.complete
          (RegistrationNativePlatformCompletionSdk.nativeAdHash coins)
          (RegistrationNativePlatformSourceBuild.pin coins)
          (admitted <$> StateT.lift allocated)
          (RegistrationNativePlatformCompletionSdk.nativePresent coins)
          (finish coins setup codec keyView failure allocation helper erased sign writer)
          token.registration (application data))).run before.1 := by
  let selectedLocal : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
  constructor
  · exact AdapterPublicServerBuildTrace.source previousLocal previousChildren coins setup codec keyView failure allocation helper erased sign writer fallback self token data
  · exact source_joint (localOps := selectedLocal) coins setup codec keyView failure allocation helper erased sign writer fallback previousChildren
      view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard

omit localOps crypto in
private theorem post_reserved
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (initial : registration.ServerInitialKdf) (previous : initial.candidate.previous_state = self.control)
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (allocated : Base AllocationReply)
    (operation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views self.known_ids reply)
    (standard : ∀ known publication pending publicKey,
      peer.begin_peer_insert self.control publication = .ok (.Ok pending) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} pending publicKey)
    (published : Option AdapterPublicServerBuildTrace.Publication)
    (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
    (after : Cut) (external next : Platform)
    (supported : (((published, .ok (reply, current)), after), next) ∈ support
      (((AdapterPublicServerBuildTrace.reserved (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
        self initial).run before).run external)) :
    AdapterPublicWrapperState.Server view views created credential current
      (project self.control ((published, .ok (reply, current)), after)).2.server := by
  unfold AdapterPublicServerBuildTrace.reserved AdapterPublicServerBuildTrace.invoke at supported
  rw [operation] at supported
  simp only [StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc, bind_map_left] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨⟨⟨allocationResult, known⟩, between⟩, called, continued⟩ := supported
  have currentMaterial := AdapterPublicWrapperState.peer_reserved view views created credential self before.1.server related
    (allocationResult, known) (footprint external (allocationResult, known) between called)
  cases allocationResult with
  | Err error =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    cases continued
    exact currentMaterial
  | Ok unitValue =>
    simp only [StateT.run_map, support_map] at continued
    obtain ⟨⟨⟨⟨pub, word⟩, final⟩, finished⟩, completed, equal⟩ := continued
    simp only [Prod.mk.injEq] at equal
    rcases equal with ⟨⟨⟨pubEq, wordEq⟩, stateEq⟩, externalEq⟩
    cases pubEq
    cases wordEq
    cases stateEq
    cases externalEq
    exact AdapterPublicServerCompletionReached.source coins setup codec keyView failure allocation helper erased sign writer fallback
      view views created credential {self with known_ids := known} before after currentMaterial initial previous parsed
      (standard known) pub (.ok (reply, current)) between next completed

omit localOps crypto in
private theorem post_lookup
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    [children : ChildOperations (RustT SourceM)]
    (hashOperation : ∀ request, (children.executeHash request).run = AdapterPublicServerCutPin.hash coins sign request)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (pin : session.ServerAuthenticationPin) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (plaintext : Slice U8) (pending : peer.CompletionLookup)
    (began : peer.begin_completion_lookup self.control pin token.registration plaintext = .ok (.Ok pending))
    (parsed : AdapterPublicServerToken.ParsedToken token)
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
    (published : Option AdapterPublicServerBuildTrace.Publication)
    (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
    (after : Cut) (external next : Platform)
    (supported : (((published, .ok (reply, current)), after), next) ∈ support
      (((AdapterPublicServerBuildTrace.lookup (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
        self pending plaintext).run before).run external)) :
    AdapterPublicWrapperState.Server view views created credential current
      (project self.control ((published, .ok (reply, current)), after)).2.server := by
  have fields := AdapterPublicServerBuildReceipt.lookup_fields self.control pin token.registration plaintext pending began
  have wrapped : ∀ length identifier,
      (beaconcrypt_public_request.server.registration_response_len (m := RustT SourceM) length identifier).run =
        pure (transport.registration_response_len length identifier) := fun _ _ => rfl
  unfold AdapterPublicServerBuildTrace.lookup AdapterPublicServerBuildTrace.invoke at supported
  simp only [RustT.run_liftRust, pure_bind] at supported
  cases requested : pending.request with
  | fail error | div =>
    simp only [requested, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and] at supported
  | ok identifier =>
    rw [requested] at supported
    simp only [] at supported
    have size : CoreModels.core.slice.Slice.len plaintext = .ok plaintext.len := rfl
    rw [size] at supported
    simp only [] at supported
    rw [wrapped] at supported
    simp only [pure_bind] at supported
    obtain ⟨capacity, sized⟩ := BeaconcryptCore.PanicFreedom.Transport.registration_response_len_total plaintext.len identifier
    rw [sized] at supported
    cases capacity with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact related
    | some capacity =>
      simp only [] at supported
      simp only [StateT.run_bind] at supported
      rw [containsOperation before related identifier] at supported
      change (((published, .ok (reply, current)), after), next) ∈ support
        (((AdapterPublicServerBuildTrace.checked self (pending.resume (views.peer self.known_ids identifier).isSome)
          (AdapterPublicServerBuildTrace.adHash (completion coins setup codec keyView failure allocation helper erased sign writer fallback) self)).run
          ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2)).run external) at supported
      have currentMaterial := AdapterPublicServerPresenceNative.material_related view views created credential self before.1.server related identifier
      unfold AdapterPublicServerBuildTrace.checked at supported
      cases resumed : pending.resume (views.peer self.known_ids identifier).isSome with
      | fail error | div =>
        rw [resumed] at supported
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and] at supported
      | ok result => cases result with
        | Err old =>
          rw [resumed] at supported
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact currentMaterial
        | Ok pendingAd =>
          rw [resumed] at supported
          have selected : registration.begin_server_completion self.control pin
              (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
              token.registration.agreement plaintext = .ok (.Ok pendingAd) := by
            cases occupied : (views.peer self.known_ids identifier).isSome <;>
              simpa only [occupied, PeerOwnership.completion_lookup_resume, fields.1, fields.2.1,
                fields.2.2.1, fields.2.2.2] using resumed
          have previous := RegistrationServerCompletionSnapshot.ad_selection self.control pin
            (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
            token.registration.agreement plaintext (.Ok pendingAd) selected
          have origin := RegistrationAd.server_ad_origin self.control pin
            (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
            token.registration.agreement plaintext pendingAd selected
          have parsedPending : AdapterPublicServerToken.ParsedBinding pendingAd.binding := by
            rw [origin.2.1]
            exact parsed
          have currentMaterial := AdapterPublicServerPresenceNative.material_related view views created credential self before.1.server related identifier
          exact AdapterPublicServerBuildPost.hashed coins setup codec keyView failure allocation helper erased sign writer fallback hashOperation
            view views created credential self
            ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2)
            currentMaterial pendingAd previous parsedPending allocated reserveOperation footprint standard
            published reply current after external next supported

omit localOps crypto in
private theorem post_after_pin
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    [children : ChildOperations (RustT SourceM)]
    (hashOperation : ∀ request, (children.executeHash request).run = AdapterPublicServerCutPin.hash coins sign request)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (plaintext : Slice U8)
    (pinned : RustM (core.option.Option session.ServerAuthenticationPin))
    (parsed : AdapterPublicServerToken.ParsedToken token)
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
    (published : Option AdapterPublicServerBuildTrace.Publication)
    (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
    (after : Cut) (external next : Platform)
    (supported : (((published, .ok (reply, current)), after), next) ∈ support
      (((AdapterPublicServerBuildPrefix.afterPin (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
        self token plaintext pinned).run before).run external)) :
    AdapterPublicWrapperState.Server view views created credential current
      (project self.control ((published, .ok (reply, current)), after)).2.server := by
  unfold AdapterPublicServerBuildPrefix.afterPin at supported
  cases pinned with
  | fail error | div =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and] at supported
  | ok optional => cases optional with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact related
    | some pin =>
      simp only [] at supported
      unfold AdapterPublicServerBuildTrace.checked at supported
      cases began : peer.begin_completion_lookup self.control pin token.registration plaintext with
      | fail error | div =>
        rw [began] at supported
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and] at supported
      | ok result => cases result with
        | Err old =>
          rw [began] at supported
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact related
        | Ok pending =>
          rw [began] at supported
          exact post_lookup coins setup codec keyView failure allocation helper erased sign writer fallback hashOperation
            view views created credential self before related pin token plaintext pending began parsed
            allocated reserveOperation footprint containsOperation standard published reply current after external next supported

theorem source_post
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
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
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
    (published : Option AdapterPublicServerBuildTrace.Publication)
    (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
    (after : Cut) (external next : Platform) :
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    (((published, .ok (reply, current)), after), next) ∈ support
      (((AdapterPublicServerBuildTrace.build (completion coins setup codec keyView failure allocation helper erased sign writer fallback)
        self token data).run before).run external) →
    AdapterPublicWrapperState.Server view views created credential current
      (project self.control ((published, .ok (reply, current)), after)).2.server := by
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
  intro supported
  rw [AdapterPublicServerBuildPrefix.normalized] at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pinned, middle⟩, between⟩, called, continued⟩ := supported
  have pinErasure := AdapterPublicServerCutPin.source coins view views created credential
    (AdapterPublicServerRecordNative.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      previousChildren coins setup codec erased)
    (AdapterPublicServerCompletionNative.writer writer) self before related edGetter mlGetter
  have projectedSupport : ((pinned, middle.1), between) ∈ support
      ((Prod.map id Prod.fst <$>
        (((beaconcrypt_public_request.server.Server.authentication_pin (m := RustT SourceM) self).run).run before)).run external) := by
    rw [StateT.run_map, support_map]
    exact ⟨((pinned, middle), between), called, rfl⟩
  rw [pinErasure] at projectedSupport
  have currentMaterial := AdapterPublicServerBuildPrefix.pin_material coins view views created credential self before.1 middle.1
    related pinned external between projectedSupport
  exact post_after_pin coins setup codec keyView failure allocation helper erased sign writer fallback (fun _ => rfl)
    view views created credential self middle currentMaterial token (AdapterPublicServerBuildPrefix.application data) pinned parsed
    allocated reserveOperation footprint containsOperation standard published reply current after between next continued

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.readback_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.readback_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.lookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.source_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.actual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.source_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildReachedContains.source_post
