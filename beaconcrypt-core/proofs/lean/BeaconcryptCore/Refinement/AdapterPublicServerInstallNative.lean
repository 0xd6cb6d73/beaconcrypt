-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful
import BeaconcryptCore.Refinement.AdapterPublicWrapperInstallation
import BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual source vacant-entry lens selects the same live native installation and exact retained kernel/AD. The native capability updates the full original World and leaves every other Server coordinate unchanged; source material then survives the actual publication control update. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerInstallNative
open AdapterPublicWrapperStorage AdapterPublicWrapperState
open BeaconcryptCore.Computational PqxdhRecordLiftInterface
variable {n : Nat}

noncomputable def capability (pending : peer.PeerInsert (alloc.vec.Vec U8)) :
    StateT (RegistrationServerFrontendCompiler.State n) ProbComp Bool :=
  RegistrationNativePlatformServerSdk.world
    (RegistrationWorldServerCompletion.capability
      (.installServer pending.peer.binding.assigned_key_id (PeerBinding.ofSession pending.peer.binding) (.known pending.peer.ratchet)))

def charged (native : RegistrationServerFrontendCompiler.State n) (pending : peer.PeerInsert (alloc.vec.Vec U8)) :
    RegistrationServerFrontendCompiler.State n :=
  { native with world := { native.world with world :=
    (PqxdhRecordLiftWorld.chargeEffect
      (.inr (.installServer pending.peer.binding.assigned_key_id (PeerBinding.ofSession pending.peer.binding) (.known pending.peer.ratchet)))
      native.world.world.1, native.world.world.2) } }

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

theorem charged_related (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) :
    Server view views created credential self (charged native pending) := by
  exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa, related.replay, related.peers⟩

theorem vacant (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (vacant : Vacant) (back : Entry → PeerMap)
    (lookedUp : PeerEntry views self.known_ids pending.peer.binding.assigned_key_id (.Vacant vacant, back)) :
    (capability pending).run native = pure (true,
      withPeer (charged native pending) pending.peer.binding.assigned_key_id
        ⟨pending.peer.binding.beacon_identity_public_key, pending.peer.ratchet, pending.peer.binding.associated_data⟩) := by
  rcases related.peers with ⟨records, reached, _sender, _identity, peers⟩
  have absent := AdapterPublicWrapperStorage.vacant_absent views self.known_ids records.records.server.peers
    pending.peer.binding.assigned_key_id vacant back peers lookedUp
  have installed := AdapterPublicWrapperInstallation.server (charged native pending).world.world.1 records
    pending.peer.binding.assigned_key_id (PeerBinding.ofSession pending.peer.binding) pending.peer.ratchet reached absent
  simp only [capability, RegistrationNativePlatformServerSdk.world, RegistrationWorldServerCompletion.capability,
    PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run]
  change (fun result => (result.1, { native with world := result.2 })) <$>
    (fun result => (result.1, { native.world with world := (result.2, native.world.world.2) })) <$>
      (PqxdhRecordLiftWorld.installServer pending.peer.binding.assigned_key_id
        (PeerBinding.ofSession pending.peer.binding) (.known pending.peer.ratchet)).run (charged native pending).world.world.1 = _
  rw [installed, map_pure, map_pure]
  unfold withPeer charged
  simp only [PqxdhRecordLiftWorld.chargeEffect, reached]
  rfl

theorem occupied (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (selected : Occupied) (back : Entry → PeerMap)
    (lookedUp : PeerEntry views self.known_ids pending.peer.binding.assigned_key_id (.Occupied selected, back)) :
    (capability pending).run native = pure (false, charged native pending) := by
  rcases related.peers with ⟨records, reached, _sender, _identity, peers⟩
  have present : (records.records.server.peers pending.peer.binding.assigned_key_id).isSome = true :=
    (peers pending.peer.binding.assigned_key_id).2.symm.trans lookedUp.1
  cases occupied : records.records.server.peers pending.peer.binding.assigned_key_id with
  | none => simp only [occupied, _root_.Option.isSome_none, Bool.false_eq_true] at present
  | some known =>
    simp only [capability, RegistrationNativePlatformServerSdk.world, RegistrationWorldServerCompletion.capability,
      PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer,
      StateT.run, PqxdhRecordLiftWorld.chargeEffect, reached, occupied, reduceCtorEq, false_and, ↓reduceIte, map_pure]
    simp only [charged, PqxdhRecordLiftWorld.chargeEffect, reached]

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {S : Type}
variable [containers : AdapterPublicWrapperRequestMonad.ContainerOperations (AdapterPublicWrapperRustT.RustT (StateT S ProbComp))]

theorem source_success (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey))
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : beaconcrypt_public_wrapper.server.Server)
    (before after : S)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.install (m := StateT S ProbComp) self pending).run).run before))
    (entryFootprint : ∀ vacant back middle,
      (.ok (.Vacant vacant, back), middle) ∈ support
        (((AdapterPublicServerInstall.entry (m := StateT S ProbComp) self.known_ids pending.peer.binding.assigned_key_id).run).run before) →
      PeerEntry views self.known_ids pending.peer.binding.assigned_key_id (.Vacant vacant, back))
    (insertFootprint : ∀ vacant back changed insertedBack middle,
      (.ok (.Vacant vacant, back), middle) ∈ support
        (((AdapterPublicServerInstall.entry (m := StateT S ProbComp) self.known_ids pending.peer.binding.assigned_key_id).run).run before) →
      (.ok (changed, insertedBack), after) ∈ support
        (((AdapterPublicServerInstall.insert (m := StateT S ProbComp) vacant
          (AdapterPublicServerInstall.remote pending publicKey)).run).run middle) →
      VacantInsert views self.known_ids pending.peer.binding.assigned_key_id back
        (AdapterPublicServerInstall.remote pending publicKey) (changed, insertedBack)) :
    (capability pending).run native = pure (true,
      withPeer (charged native pending) pending.peer.binding.assigned_key_id
        ⟨pending.peer.binding.beacon_identity_public_key, pending.peer.ratchet, pending.peer.binding.associated_data⟩) ∧
    Server view views created credential current
      { withPeer (charged native pending) pending.peer.binding.assigned_key_id
        ⟨pending.peer.binding.beacon_identity_public_key, pending.peer.ratchet, pending.peer.binding.associated_data⟩
        with control := pending.next } := by
  obtain ⟨selected, back, changed, insertedBack, middle, lookedUp, inserted, _bytes, _identifier, same⟩ :=
    AdapterPublicServerInstallStateful.success self pending publicKey parsed response current before after supported
  refine ⟨vacant view views created credential self native related pending selected back
    (entryFootprint selected back middle lookedUp), ?_⟩
  rw [same]
  exact AdapterPublicServerInstallMaterial.vacant view views created credential self (charged native pending)
    (charged_related view views created credential self native related pending) pending publicKey
    back (changed, insertedBack) (insertFootprint selected back changed insertedBack middle lookedUp inserted)
theorem source_none (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey))
    (current : beaconcrypt_public_wrapper.server.Server) (before after : S)
    (supported : (.ok (.None, current), after) ∈ support
      (((AdapterPublicServerBuildBody.install (m := StateT S ProbComp) self pending).run).run before))
    (entryFootprint : ∀ selected back middle,
      (.ok (.Occupied selected, back), middle) ∈ support
        (((AdapterPublicServerInstall.entry (m := StateT S ProbComp) self.known_ids pending.peer.binding.assigned_key_id).run).run before) →
      PeerEntry views self.known_ids pending.peer.binding.assigned_key_id (.Occupied selected, back)) :
    (capability pending).run native = pure (false, charged native pending) ∧
      Server view views created credential current (charged native pending) := by
  rw [AdapterPublicServerInstall.install self pending publicKey parsed] at supported
  simp only [AdapterPublicServerInstall.afterParse, AdapterPublicWrapperRustT.RustT.run_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨entryReply, middle⟩, lookedUp, continued⟩ := supported
  cases entryReply with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok pair =>
    rcases pair with ⟨entry, back⟩
    cases entry with
    | Occupied selected =>
      simp only [AdapterPublicWrapperRustT.RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, RustM.ok.injEq, true_and] at continued
      rcases continued with ⟨sameObject, sameState⟩
      cases sameObject
      cases sameState
      have footprint := entryFootprint selected back after lookedUp
      exact ⟨occupied view views created credential self native related pending selected back footprint,
        AdapterPublicServerInstallMaterial.entry view views created credential self (charged native pending)
          (charged_related view views created credential self native related pending) pending.peer.binding.assigned_key_id
          (.Occupied selected, back) footprint⟩
    | Vacant selected =>
      dsimp only at continued
      simp only [AdapterPublicWrapperRustT.RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨insertReply, final⟩, _inserted, returned⟩ := continued
      cases insertReply with
      | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, reduceCtorEq, false_and] at returned
      | ok pair =>
        rcases pair with ⟨changed, insertedBack⟩
        simp only [AdapterPublicWrapperRustT.RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at returned

end BeaconcryptCore.Refinement.AdapterPublicServerInstallNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.charged_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.charged_related

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.vacant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.vacant

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.occupied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.occupied

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.source_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.source_success

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.source_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallNative.source_none
