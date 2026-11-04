-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual known-kernel installation tail is deterministic administrative work, including the refused installation charge. Its exact pure result supplies only the native bookkeeping projection of the actual source installer. Source response bytes and returned material are proved equal using the individual standard-container footprints and the authentication-derived parse receipt; they are never defined from an unrelated successful run. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
variable {n : Nat} {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem known_pure (keyId : U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (before : PqxdhRecordLiftWorld.State n) :
    ∃ result, (PqxdhRecordLiftWorld.installServer keyId binding (.known kernel)).run before = pure result := by
  cases stored : before.server with
  | none => exact ⟨(false, before), by simp only [PqxdhRecordLiftWorld.installServer, StateT.run, stored]⟩
  | some server =>
    simp only [PqxdhRecordLiftWorld.installServer, StateT.run, stored]
    split
    · simp only [PqxdhRecordLiftWorld.resolve]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

private theorem capability_pure (pending : peer.PeerInsert (alloc.vec.Vec U8))
    (before : RegistrationServerFrontendCompiler.State n) :
    ∃ result, (AdapterPublicServerInstallNative.capability pending).run before = pure result := by
  obtain ⟨result, computed⟩ := known_pure pending.peer.binding.assigned_key_id
    (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding) pending.peer.ratchet
    (AdapterPublicServerInstallNative.charged before pending).world.world.1
  simp only [AdapterPublicServerInstallNative.capability, RegistrationNativePlatformServerSdk.world,
    RegistrationWorldServerCompletion.capability, PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run]
  change ∃ output, (fun result => (result.1, {before with world := result.2})) <$>
    ((fun result => (result.1, {before.world with world := (result.2, before.world.world.2)})) <$>
      (PqxdhRecordLiftWorld.installServer pending.peer.binding.assigned_key_id
        (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding) (.known pending.peer.ratchet)).run
          (AdapterPublicServerInstallNative.charged before pending).world.world.1) = pure output
  rw [computed, map_pure, map_pure]
  exact ⟨_, rfl⟩

private theorem world_pure {A : Type} (value : A) :
    RegistrationNativePlatformServerSdk.world (pure value : StateT (RegistrationServerRootCompiler.Local n) m A) =
      (pure value : StateT (RegistrationServerFrontendCompiler.State n) m A) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, {before with world := result.2})) <$> pure (value, before.world) = pure (value, before)
  rw [map_pure]

theorem native_pure (coins : QueryImpl unifSpec m) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) :
    ∃ result, (AdapterPublicServerPublicationInstall.native coins control published).run before = pure result := by
  cases published with
  | fail error =>
    simp only [AdapterPublicServerPublicationInstall.native, RegistrationNativePlatformServerCompletion.continueResult, world_pure, pure_bind]
    exact ⟨(.fail error, before), rfl⟩
  | div =>
    simp only [AdapterPublicServerPublicationInstall.native, RegistrationNativePlatformServerCompletion.continueResult, world_pure, pure_bind]
    exact ⟨(.div, before), rfl⟩
  | ok result => cases result with
    | Err rejected =>
      simp only [AdapterPublicServerPublicationInstall.native, RegistrationNativePlatformServerCompletion.continueResult, world_pure, pure_bind]
      exact ⟨(.ok none, {before with control := rejected}), rfl⟩
    | Ok published =>
      obtain ⟨result, began, _retained⟩ := PeerOwnership.peer_insert_begin_retains control published
      cases result with
      | Err rejected =>
        simp only [AdapterPublicServerPublicationInstall.native, RegistrationNativePlatformServerCompletion.continueResult,
          RegistrationNativePlatformServerCompletion.installWith, began, world_pure, pure_bind]
        exact ⟨(.ok none, {before with control := rejected}), rfl⟩
      | Ok pending =>
        rw [AdapterPublicServerPublicationInstall.native_insert coins control published pending began]
        obtain ⟨⟨inserted, after⟩, computed⟩ := capability_pure pending before
        change ∃ result, (do
          let replied ← simulateQ coins ((AdapterPublicServerInstallNative.capability pending).run before)
          (RegistrationNativePlatformServerSdk.commit
            ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
              peer.PublicationFinish (alloc.vec.Vec U8)).finish replied.1)).run replied.2) = pure result
        rw [computed, simulateQ_pure, pure_bind]
        cases inserted <;> exact ⟨_, rfl⟩

noncomputable def result (coins : QueryImpl unifSpec m) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) :
    RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerFrontendCompiler.State n :=
  (native_pure coins control published before).choose

theorem result_run (coins : QueryImpl unifSpec m) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (before : RegistrationServerFrontendCompiler.State n) :
    (AdapterPublicServerPublicationInstall.native coins control published).run before = pure (result coins control published before) :=
  (native_pure coins control published before).choose_spec
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT m)]
variable {mlSource : RegistrationNativeMldsa.Source} {KemSK : Type}

theorem source (coins : QueryImpl unifSpec m)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
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
    (fun word => (AdapterPublicServerPublicationInstall.project word, (result coins self.control published before).2)) <$>
      AdapterPublicServerPublication.afterPublication (m := m) self published =
        (AdapterPublicServerPublicationInstall.native coins self.control published).run before := by
  obtain ⟨word, after, actual, nativeComputed, _material⟩ := AdapterPublicServerPublicationInstall.publication coins
    view views created credential self before related initial previous parsed published retained standard
  rw [actual, map_pure, result_run]
  have compared := congrArg (fun work =>
    (fun pair : RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerFrontendCompiler.State n =>
      (pair.1, (result coins self.control published before).2)) <$> work)
      (nativeComputed.symm.trans (result_run coins self.control published before))
  simpa only [map_pure, Prod.mk.eta] using compared

end BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection.native_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection.native_pure
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection.result_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection.result_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionProjection.source
