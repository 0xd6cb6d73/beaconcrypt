-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The exact actual known-kernel administrative tail is independent of the base effect monad and coin interpreter. This supplies one shared native bookkeeping result when the original source installer runs under the additional private signing cut. Only administrative installation is normalized; allocation and crypto remain in the earlier common stateful run. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
variable {n : Nat} {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem world_pure {A : Type} (value : A) :
    RegistrationNativePlatformServerSdk.world (pure value : StateT (RegistrationServerRootCompiler.Local n) m A) =
      (pure value : StateT (RegistrationServerFrontendCompiler.State n) m A) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, {before with world := result.2})) <$> pure (value, before.world) = pure (value, before)
  rw [map_pure]

theorem interpret (coins : QueryImpl unifSpec m) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) :
    (AdapterPublicServerPublicationInstall.native coins control published).run before =
      simulateQ coins ((AdapterPublicServerPublicationInstall.native (QueryImpl.id' unifSpec) control published).run before) := by
  cases published with
  | fail error | div =>
    simp only [AdapterPublicServerPublicationInstall.native, RegistrationNativePlatformServerCompletion.continueResult,
      world_pure, pure_bind]
    exact (simulateQ_pure coins _).symm
  | ok result => cases result with
    | Err rejected =>
      simp only [AdapterPublicServerPublicationInstall.native, RegistrationNativePlatformServerCompletion.continueResult,
        world_pure, pure_bind]
      exact (simulateQ_pure coins _).symm
    | Ok published =>
      obtain ⟨result, began, _retained⟩ := PeerOwnership.peer_insert_begin_retains control published
      cases result with
      | Err rejected =>
        simp only [AdapterPublicServerPublicationInstall.native, RegistrationNativePlatformServerCompletion.continueResult,
          RegistrationNativePlatformServerCompletion.installWith, began, world_pure, pure_bind]
        exact (simulateQ_pure coins _).symm
      | Ok pending =>
        rw [AdapterPublicServerPublicationInstall.native_insert coins control published pending began,
          AdapterPublicServerPublicationInstall.native_insert (QueryImpl.id' unifSpec) control published pending began]
        change (do let result ← simulateQ coins ((AdapterPublicServerInstallNative.capability pending).run before)
                   (RegistrationNativePlatformServerSdk.commit
                     ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
                       peer.PublicationFinish (alloc.vec.Vec U8)).finish result.1)).run result.2) =
          simulateQ coins (do let result ← simulateQ (QueryImpl.id' unifSpec) ((AdapterPublicServerInstallNative.capability pending).run before)
                              (RegistrationNativePlatformServerSdk.commit
                                ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
                                  peer.PublicationFinish (alloc.vec.Vec U8)).finish result.1)).run result.2)
        rw [simulateQ_id', simulateQ_bind]
        apply bind_congr
        rintro ⟨inserted, after⟩
        cases inserted <;> exact (simulateQ_pure coins _).symm

noncomputable def result (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) :
    RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerFrontendCompiler.State n :=
  AdapterPublicServerCompletionProjection.result (QueryImpl.id' unifSpec) control published before

theorem native_run (coins : QueryImpl unifSpec m) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) :
    (AdapterPublicServerPublicationInstall.native coins control published).run before = pure (result control published before) := by
  rw [interpret, AdapterPublicServerCompletionProjection.result_run, simulateQ_pure]
  rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT m)]
variable {mlSource : RegistrationNativeMldsa.Source} {KemSK : Type}

theorem source (coins : QueryImpl unifSpec m)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self before)
    (initial : registration.ServerInitialKdf)
    (previous : initial.candidate.previous_state = self.control)
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (retained : RegistrationServerSourceCompletionReceipt.Post initial published)
    (standard : ∀ publication pending publicKey,
      published = .ok (.Ok publication) → peer.begin_peer_insert self.control publication = .ok (.Ok pending) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := m) views self pending publicKey) :
    (fun word => (AdapterPublicServerPublicationInstall.project word, (result self.control published before).2)) <$>
      AdapterPublicServerPublication.afterPublication (m := m) self published =
        (AdapterPublicServerPublicationInstall.native coins self.control published).run before := by
  obtain ⟨word, after, actual, nativeComputed, _material⟩ := AdapterPublicServerPublicationInstall.publication coins
    view views created credential self before related initial previous parsed published retained standard
  rw [actual, map_pure, native_run]
  have compared := congrArg (fun work =>
    (fun pair : RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerFrontendCompiler.State n =>
      (pair.1, (result self.control published before).2)) <$> work)
      (nativeComputed.symm.trans (native_run coins self.control published before))
  simpa only [map_pure, Prod.mk.eta] using compared

end BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical.interpret
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical.native_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical.source
