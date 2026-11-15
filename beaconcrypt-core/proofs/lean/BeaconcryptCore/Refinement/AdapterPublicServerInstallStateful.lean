-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Successful actual source installation has a reached vacant-entry callback and a reached insertion callback on the same run, with their complete shared poststates. Narrow standard insertion footprints then derive the actual stored Server material update. This is a local object correspondence, not identification of the outer native profile. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperStorage
open AdapterPublicWrapperState
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {S : Type}
variable [containers : ContainerOperations (RustT (StateT S ProbComp))]

noncomputable section
theorem success (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey))
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : beaconcrypt_public_wrapper.server.Server)
    (before after : S)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.install (m := StateT S ProbComp) self pending).run).run before)) :
    ∃ vacant back changed insertedBack middle,
      (.ok (.Vacant vacant, back), middle) ∈ support
        (((AdapterPublicServerInstall.entry (m := StateT S ProbComp) self.known_ids pending.peer.binding.assigned_key_id).run).run before) ∧
      (.ok (changed, insertedBack), after) ∈ support
        (((AdapterPublicServerInstall.insert (m := StateT S ProbComp) vacant
          (AdapterPublicServerInstall.remote pending publicKey)).run).run middle) ∧
      response.serialized = pending.encoded ∧ response.kid = pending.peer.binding.assigned_key_id ∧
      current = { self with known_ids := back (.Vacant (insertedBack changed)), control := pending.next } := by
  rw [AdapterPublicServerInstall.install self pending publicKey parsed] at supported
  simp only [AdapterPublicServerInstall.afterParse, RustT.run_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨entryReply, middle⟩, lookedUp, continued⟩ := supported
  cases entryReply with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok pair =>
    rcases pair with ⟨entry, back⟩
    cases entry with
    | Occupied occupied => simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
    | Vacant vacant =>
      dsimp only at continued
      simp only [RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨insertReply, final⟩, inserted, returned⟩ := continued
      cases insertReply with
      | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, reduceCtorEq, false_and] at returned
      | ok pair =>
        rcases pair with ⟨changed, insertedBack⟩
        simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, RustM.ok.injEq, core.option.Option.Some, _root_.Option.some.injEq] at returned
        obtain ⟨⟨responseSame, stateSame⟩, sharedSame⟩ := returned
        cases sharedSame
        cases stateSame
        cases responseSame
        exact ⟨vacant, back, changed, insertedBack, middle, lookedUp, inserted, rfl, rfl, rfl⟩

variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}
theorem material_correspondence (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey))
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : beaconcrypt_public_wrapper.server.Server)
    (before after : S)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.install (m := StateT S ProbComp) self pending).run).run before))
    (insertFootprint : ∀ vacant back changed insertedBack middle,
      (.ok (.Vacant vacant, back), middle) ∈ support
        (((AdapterPublicServerInstall.entry (m := StateT S ProbComp) self.known_ids pending.peer.binding.assigned_key_id).run).run before) →
      (.ok (changed, insertedBack), after) ∈ support
        (((AdapterPublicServerInstall.insert (m := StateT S ProbComp) vacant
          (AdapterPublicServerInstall.remote pending publicKey)).run).run middle) →
      VacantInsert views self.known_ids pending.peer.binding.assigned_key_id back
        (AdapterPublicServerInstall.remote pending publicKey) (changed, insertedBack)) :
    Server view views created credential current
      { withPeer native pending.peer.binding.assigned_key_id
        ⟨pending.peer.binding.beacon_identity_public_key, pending.peer.ratchet, pending.peer.binding.associated_data⟩
        with control := pending.next } := by
  obtain ⟨vacant, back, changed, insertedBack, middle, lookedUp, inserted, _bytes, _identifier, same⟩ :=
    success self pending publicKey parsed response current before after supported
  rw [same]
  exact AdapterPublicServerInstallMaterial.vacant view views created credential self native related pending publicKey
    back (changed, insertedBack) (insertFootprint vacant back changed insertedBack middle lookedUp inserted)
end
end BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful.success

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful.material_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful.material_correspondence
