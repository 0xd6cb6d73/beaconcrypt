-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace
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
/-! The literal Server build prefix retains the actual map-reservation result and returned container on both outcomes. Its logical native projection executes that same allocation with its complete platform poststate before the already derived first-record/publication lifetime. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix
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

noncomputable def project (control : pqxdh.ServerState) (result : AdapterPublicServerBuildTrace.Word × Cut) :
    RustM (Option (U64 × alloc.vec.Vec U8)) × Native :=
  match result.1.1 with
  | none => (AdapterPublicServerPublicationInstall.project result.1.2, result.2.1)
  | some published => AdapterPublicServerCompletionLifetime.project control ((published, result.1.2), result.2)

abbrev AllocationReply := core.result.Result Unit platform.ReserveError × PeerMap

def admitted (reply : AllocationReply) : Bool :=
  match reply.1 with
  | .Err _ => false
  | .Ok _ => true

def reserveNative (allocated : Base AllocationReply) : NativeM Bool := admitted <$> StateT.lift allocated


noncomputable def finish
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
 : RegistrationNativePlatformCompletionSdk.Completion n Base (alloc.vec.Vec U8) := RegistrationNativePlatformSourceBuild.finishSource coins setup codec
  (RegistrationNativePlatformSourceSeal.sealing coins setup codec keyView failure allocation)
  (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer

noncomputable def completion
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)
 : Server → registration.ServerInitialKdf → SourceM (AdapterPublicServerBuildTrace.Publication × RustM Reply) := AdapterPublicServerBuildTrace.complete coins setup codec keyView failure allocation helper erased sign writer fallback


theorem reserved
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
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
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
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} pending publicKey) :
    project self.control <$>
      ((AdapterPublicServerBuildTrace.reserved (m := SourceM) (completion coins setup codec keyView failure allocation helper erased sign writer fallback) self initial).run before) =
    (do
      let ok ← reserveNative allocated
      if ok then
        RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.fromInitial (finish coins setup codec keyView failure allocation helper erased sign writer) self.control initial)
      else pure (.ok none)).run before.1 := by
  unfold AdapterPublicServerBuildTrace.reserved AdapterPublicServerBuildTrace.invoke
  rw [operation]
  simp only [StateT.run_bind, StateT.run_map, StateT.run_lift, map_bind]
  unfold reserveNative
  simp only [StateT.run_map, StateT.run_lift, bind_map_left]
  apply StateT.ext
  intro external
  simp only [StateT.run_bind, StateT.run_map, map_pure, pure_bind, bind_assoc]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨reply, between⟩ supported
  have currentMaterial := AdapterPublicWrapperState.peer_reserved view views created credential self before.1.server related reply (footprint external reply between supported)
  rcases reply with ⟨allocationResult, known⟩
  cases allocationResult with
  | Err error => simp only [admitted, StateT.run_pure, map_pure, project, AdapterPublicServerPublicationInstall.project, AdapterPublicServerPublicationInstall.output, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  | Ok unitValue =>
    simp only [admitted, ↓reduceIte, StateT.run_map, Functor.map_map]
    have stage := AdapterPublicServerCompletionLifetime.coupled coins setup codec keyView failure allocation helper erased sign writer fallback
      view views created credential {self with known_ids := known} before currentMaterial initial previous parsed (standard known)
    simpa only [completion, AdapterPublicServerBuildTrace.complete, project, finish, StateT.run_map] using congrArg (fun work => work.run between) stage


noncomputable def lookupNative
    (coins : QueryImpl unifSpec Base) (reserve : NativeM Bool)
    (done : RegistrationNativePlatformCompletionSdk.Completion n Base (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (pending : peer.CompletionLookup) (plaintext : Slice U8) :
    NativeM (RustM (Option (U64 × alloc.vec.Vec U8))) :=
  match pending.request with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok identifier =>
    if RegistrationServerSdkSource.preflight plaintext identifier then do
      let occupied ← RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier)
      match pending.resume occupied with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok initial) => do
        let ok ← reserve
        if ok then
          RegistrationNativePlatformExperiment.server
            (RegistrationNativePlatformCompletionSdk.fromInitial done control initial)
        else pure (.ok none)
    else pure (.ok none)


omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
private theorem present_run (coins : QueryImpl unifSpec Base)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Native)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server) (identifier : U64) :
    (RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier)).run before =
      pure ((views.peer self.known_ids identifier).isSome,
        {before with server := AdapterPublicServerPresenceNative.charged before.server identifier}) := by
  rw [AdapterPublicServerSourceLens.server_run,
    AdapterPublicServerPresenceNative.source coins view views created credential self before.server related identifier, map_pure]

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

    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
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
      rw [containsOperation identifier]
      simp only [StateT.run_bind, StateT.run_map, map_bind]
      have present := present_run coins view views created credential self before.1 related identifier
      unfold RegistrationNativePlatformCutErasure.liftWorld
      rw [present]
      dsimp only [StateT.run] at present
      simp only [StateT.run, present, map_pure, pure_bind]
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
        | Ok initial =>
          have beganInitial : registration.begin_server_completion self.control pin
              (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
              token.registration.agreement plaintext = .ok (.Ok initial) := by
            cases occupied : (views.peer self.known_ids identifier).isSome <;>
              simpa only [occupied, PeerOwnership.completion_lookup_resume, fields.1, fields.2.1,
                fields.2.2.1, fields.2.2.2] using resumed
          have previous := RegistrationServerCompletionSnapshot.initial self.control pin
            (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
            token.registration.agreement plaintext
          rw [beganInitial] at previous
          have parsedInitial := AdapterPublicServerCompletionInstall.initial_parsed self.control pin
            (if (views.peer self.known_ids identifier).isSome then .Occupied else .Available)
            token plaintext initial beganInitial parsed
          have currentMaterial := AdapterPublicServerPresenceNative.material_related view views created credential self before.1.server related identifier
          exact reserved coins setup codec keyView failure allocation helper erased sign writer fallback
            view views created credential self
            ({before.1 with server := AdapterPublicServerPresenceNative.charged before.1.server identifier}, before.2)
            currentMaterial initial (previous (.Ok initial) rfl) parsedInitial allocated reserveOperation footprint standard


omit material primitive containers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem lookup_global (coins : QueryImpl unifSpec Base) (allocated : Base AllocationReply)
    (done : RegistrationNativePlatformCompletionSdk.Completion n Base (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (pending : peer.CompletionLookup) (plaintext : Slice U8) :
    lookupNative (KemSK := KemSK) (mlSource := mlSource) coins (reserveNative allocated) done control pending plaintext =
      RegistrationNativePlatformExperiment.server (match pending.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok identifier => if RegistrationServerSdkSource.preflight plaintext identifier then do
          let occupied ← RegistrationNativePlatformCompletionSdk.nativePresent coins identifier
          RegistrationNativePlatformCompletionSdk.afterOccupancy
            (admitted <$> StateT.lift allocated) done control pending occupied
        else pure (.ok none)) := by
  unfold lookupNative
  cases requested : pending.request with
  | fail error | div => exact (AdapterPublicServerSourceLens.server_pure _).symm
  | ok identifier =>
    simp only []
    split
    · rw [AdapterPublicServerSourceLens.server_bind]
      apply bind_congr
      intro occupied
      unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
      cases pending.resume occupied with
      | fail error | div => exact (AdapterPublicServerSourceLens.server_pure _).symm
      | ok result => cases result with
        | Err _ => exact (AdapterPublicServerSourceLens.server_pure _).symm
        | Ok initial =>
          simp only [map_eq_pure_bind, AdapterPublicServerSourceLens.server_bind, AdapterPublicServerSourceLens.server_lift,
            bind_assoc, pure_bind, reserveNative]
          apply bind_congr
          intro reply
          cases admitted reply <;> simp only [Bool.false_eq_true, ↓reduceIte, AdapterPublicServerSourceLens.server_pure]
    · exact (AdapterPublicServerSourceLens.server_pure _).symm

omit primitive containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] in
theorem pin_material (coins : QueryImpl unifSpec Base)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before after : Native)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (reply : RustM (core.option.Option session.ServerAuthenticationPin)) (external next : Platform)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceBuild.pin coins)).run before).run external)) :
    AdapterPublicWrapperState.Server view views created credential self after.server := by
  unfold RegistrationNativePlatformExperiment.server RegistrationNativePlatformSourceBuild.pin at supported
  simp only [StateT.run, Functor.map_map] at supported
  change ((reply, after), next) ∈ support
    (((fun result : RegistrationNativeServerPinRecompute.PinReply × PqxdhRecordLiftWorld.State n =>
      (result.1, AdapterPublicAgreementNativeWorldMap.putWorld before result.2)) <$>
      simulateQ coins ((RegistrationNativeServerPinRecompute.native before.server.pin.binding before.server.pin.public_key).run before.server.world.world.1)).run external) at supported
  rw [StateT.run_map] at supported
  simp only [support_map] at supported
  obtain ⟨⟨⟨result, world⟩, between⟩, called, equal⟩ := supported
  have nativeSupport := RegistrationNativePlatformHashReceipt.native_support coins _ (result, world) external between called
  have kept := AdapterPublicServerPrefixMaterial.pin_server before.server.pin.binding before.server.pin.public_key
    before.server.world.world.1 world result nativeSupport
  have nativeEq := congrArg (fun result => result.1.2) equal
  change AdapterPublicAgreementNativeWorldMap.putWorld before world = after at nativeEq
  rw [← nativeEq]
  exact AdapterPublicServerPrefixMaterial.related_world view views created credential self before related world kept


noncomputable def afterPin
    (done : Server → registration.ServerInitialKdf → SourceM (AdapterPublicServerBuildTrace.Publication × RustM Reply))
    (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (plaintext : Slice U8)
    (pinned : RustM (core.option.Option session.ServerAuthenticationPin)) : SourceM AdapterPublicServerBuildTrace.Word :=
  match pinned with
  | .fail error => pure (none, .fail error)
  | .div => pure (none, .div)
  | .ok .None => pure (none, .ok (.None, self))
  | .ok (.Some pin) => AdapterPublicServerBuildTrace.checked self
      (peer.begin_completion_lookup self.control pin token.registration plaintext)
      (fun pending => AdapterPublicServerBuildTrace.lookup done self pending plaintext)

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

    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
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
    project self.control <$>
      ((afterPin (completion coins setup codec keyView failure allocation helper erased sign writer fallback) self token plaintext pinned).run before) =
    (RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformCompletionSdk.afterPin
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
          rw [lookup coins setup codec keyView failure allocation helper erased sign writer fallback
            view views created credential self before related pin token plaintext pending began parsed
            allocated reserveOperation footprint containsOperation standard, lookup_global]
          rfl


def application (data : core.option.Option (Slice U8)) : Slice U8 :=
  match data with
  | .None => transport.REGISTRATION_WITNESS.to_slice
  | .Some bytes => bytes

omit primitive in
theorem normalized
    [LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
      (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
    [CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
      (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
    [ChildOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
      (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
    (done : Server → registration.ServerInitialKdf → SourceM (AdapterPublicServerBuildTrace.Publication × RustM Reply))
    (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) :
    AdapterPublicServerBuildTrace.build done self token data = (do
      let pinned ← (beaconcrypt_public_request.server.Server.authentication_pin (m := RustT SourceM) self).run
      afterPin done self token (application data) pinned) := by
  cases data <;>
    simp only [AdapterPublicServerBuildTrace.build, AdapterPublicServerBuildTrace.invoke,
      transport.normalize_registration_application, RustT.run_liftRust, pure_bind,
      beaconcrypt_public_wrapper.server.registration_application_bytes, lift, afterPin, application]
  all_goals
    apply bind_congr
    intro result
    cases result with
    | fail error | div => rfl
    | ok optional => cases optional <;> rfl

omit material platform ed primitive containers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem complete_global_run
    (pin : StateT (RegistrationServerFrontendCompiler.State n) Base
      (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) Base Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) Base Bool)
    (done : RegistrationNativePlatformCompletionSdk.Completion n Base (alloc.vec.Vec U8))
    (token : peer.ConsumedRegistration) (plaintext : Slice U8) (before : Native) :
    (RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformCompletionSdk.complete pin reserve present done token plaintext)).run before = (do
      let (pinned, current) ← (RegistrationNativePlatformExperiment.server pin).run before
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.afterPin reserve present done
        before.server.control token plaintext pinned)).run current) := by
  rw [AdapterPublicServerSourceLens.server_run, RegistrationNativePlatformCompletionSdk.complete_run]
  simp only [AdapterPublicServerSourceLens.server_run, map_bind, bind_map_left]

end BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.reserved

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.lookup

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.lookup_global' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.lookup_global

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.pin_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.pin_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.after_pin

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.normalized

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.complete_global_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix.complete_global_run
