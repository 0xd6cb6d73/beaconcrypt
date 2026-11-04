-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace
import BeaconcryptCore.Refinement.AdapterPublicServerTailMaterial
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Source response publication and its actual mutable installer retain the original returned Server object while their proved administrative projection equals the actual native SDK installation/commit. The private hash cut is erased only after the same reached source prefix. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT Platform ProbComp
local notation "SourceM" => StateT Cut Base
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]

noncomputable def project (control : pqxdh.ServerState)
    (result : ((RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × RustM AdapterPublicServerBuildBody.Reply) × Cut)) :
    RustM (Option (U64 × alloc.vec.Vec U8)) × Native :=
  (AdapterPublicServerPublicationInstall.project result.1.2,
    {result.2.1 with server := (AdapterPublicServerTailCanonical.result control result.1.1 result.2.1.server).2})

def liftedCoins (coins : QueryImpl unifSpec Base) : QueryImpl unifSpec SourceM := fun query => StateT.lift (coins query)

theorem suffix (coins : QueryImpl unifSpec Base)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (current : Cut)
    (related : Server view views created credential self current.1.server)
    (initial : registration.ServerInitialKdf)
    (previous : initial.candidate.previous_state = self.control)
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (retained : RegistrationServerSourceCompletionReceipt.Post initial published)
    (standard : ∀ publication pending publicKey,
      published = .ok (.Ok publication) → peer.begin_peer_insert self.control publication = .ok (.Ok pending) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views self pending publicKey) :
    (fun result => project self.control ((published, result.1), result.2)) <$>
      ((AdapterPublicServerPublication.afterPublication (m := SourceM) self published).run current) =
        (RegistrationNativePlatformExperiment.server
          (AdapterPublicServerPublicationInstall.native coins self.control published)).run current.1 := by
  rw [AdapterPublicServerSourceLens.server_run, AdapterPublicServerTailCanonical.native_run, map_pure]
  apply StateT.ext
  intro external
  obtain ⟨word, actual, observed, _material⟩ := AdapterPublicServerTailMaterial.source (liftedCoins coins)
    view views created credential self current.1.server related initial previous parsed published retained standard current external
  rw [actual, StateT.run_pure, map_pure, StateT.run_pure]
  simp only [project, observed]
  rfl
variable {E I Reader Response : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]

theorem coupled (coins : QueryImpl unifSpec Base)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK mlSource Base RegistrationSigningShared.SignReply)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : Cut)
    (related : Server view views created credential self before.1.server)
    (initial : registration.ServerInitialKdf)
    (previous : initial.candidate.previous_state = self.control)
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (standard : ∀ publication pending publicKey,
      peer.begin_peer_insert self.control publication = .ok (.Ok pending) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views self pending publicKey) :
    project self.control <$>
      ((AdapterPublicServerCompletionSource.receipt
        (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
        (AdapterPublicServerCompletionNative.outgoing coins sign) fallback coins setup codec keyView failure allocation helper erased
        (AdapterPublicServerCompletionNative.writer writer) self initial).run before) =
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformCompletionSdk.fromInitial
          (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
            (RegistrationNativePlatformSourceSeal.sealing coins setup codec keyView failure allocation)
            (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer) self.control initial)).run before.1 := by
  rw [AdapterPublicServerCompletionLocal.fromInitial_factor]
  have projectionEq := AdapterPublicServerCompletionNative.erasure coins setup codec keyView failure allocation helper erased sign writer fallback initial before
  unfold AdapterPublicServerCompletionSource.receipt
  simp only [StateT.run_bind, bind_pure_comp, map_bind]
  rw [← AdapterPublicServerCompletionLocal.native_local]
  rw [← projectionEq, bind_map_left]
  apply StateT.ext
  intro external
  simp only [StateT.run_bind, StateT.run_map]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨published, current⟩, between⟩ supported
  obtain ⟨retained, currentMaterial⟩ := AdapterPublicServerCompletionTrace.source_receipt coins setup codec keyView failure allocation helper erased sign writer fallback initial
    view views created credential self before current related external between published supported
  have continued := suffix coins view views created credential self current currentMaterial initial previous parsed published retained
    (fun publication pending publicKey _ began reparsed => standard publication pending publicKey began reparsed)
  simpa only [StateT.run_map, Functor.map_map, Prod.map, id_eq] using congrArg (fun work => work.run between) continued

theorem source_marginal
    (previousLocal : LocalOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (coins : QueryImpl unifSpec Base)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK mlSource Base RegistrationSigningShared.SignReply)
    (self : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf) :
    letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    (AdapterPublicServerBuildBody.record (m := SourceM) self initial).run =
      Prod.snd <$> AdapterPublicServerCompletionSource.receipt
        (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
        (AdapterPublicServerCompletionNative.outgoing coins sign) fallback coins setup codec keyView failure allocation helper erased
        (AdapterPublicServerCompletionNative.writer writer) self initial := by
  let : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  rw [AdapterPublicServerCompletionSource.source _ (AdapterPublicServerCompletionNative.outgoing coins sign) fallback AdapterPublicServerCompletionNative.hom previousLocal previousChildren
    coins setup codec keyView failure allocation helper erased (AdapterPublicServerCompletionNative.writer writer) self initial]
  exact (AdapterPublicServerCompletionSource.receipt_erasure _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

end BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime.suffix

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime.coupled

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime.source_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime.source_marginal
