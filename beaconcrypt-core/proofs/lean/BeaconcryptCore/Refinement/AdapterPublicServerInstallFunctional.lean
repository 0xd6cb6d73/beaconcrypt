-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerInstallNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Narrow normality and mutable-lens footprints for the two standard container operations derive the complete actual source installer result and native capability state. The allocation reservation is earlier and remains separate; this interface applies at the resulting reserved map. Actual Core insertion setup derives the publication rollback control. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerInstallFunctional
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperStorage AdapterPublicWrapperState
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [containers : ContainerOperations (RustT m)]

structure Standard (views : Views) (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey) where
  entryReply : Entry × (Entry → PeerMap)
  entryNormal : AdapterPublicServerInstall.entry (m := m) self.known_ids pending.peer.binding.assigned_key_id = pure entryReply
  entryFootprint : PeerEntry views self.known_ids pending.peer.binding.assigned_key_id entryReply
  insertNormal : ∀ vacant back, entryReply = (.Vacant vacant, back) →
    ∃ result, AdapterPublicServerInstall.insert (m := m) vacant (AdapterPublicServerInstall.remote pending publicKey) = pure result ∧
      VacantInsert views self.known_ids pending.peer.binding.assigned_key_id back (AdapterPublicServerInstall.remote pending publicKey) result

variable {source : RegistrationNativeMldsa.Source} {KemSK : Type} {n : Nat}

theorem functional (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (published : registration.PublishedServerResponse (alloc.vec.Vec U8))
    (pending : peer.PeerInsert (alloc.vec.Vec U8))
    (began : peer.begin_peer_insert self.control published = .ok (.Ok pending))
    (publicKey : ed.PublicKey)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey))
    (standard : Standard (m := m) views self pending publicKey) :
    ∃ reply current after,
      AdapterPublicServerBuildBody.install (m := m) self pending = pure (reply, current) ∧
      (AdapterPublicServerInstallNative.capability pending).run native = pure (_root_.Option.isSome reply, after) ∧
      Server view views created credential current
        { after with control := if _root_.Option.isSome reply then pending.next else pending.previous } ∧
      (∀ response, reply = .Some response → response.serialized = pending.encoded ∧ response.kid = pending.peer.binding.assigned_key_id) := by
  obtain ⟨result, actual, retained⟩ := PeerOwnership.peer_insert_begin_retains self.control published
  have same : result = .Ok pending := RustM.ok.inj (actual.symm.trans began)
  rw [same] at retained
  have previous : pending.previous = native.control := retained.1.trans related.control
  rw [AdapterPublicServerInstall.install self pending publicKey parsed]
  rcases standard with ⟨entryReply, entryNormal, entryFootprint, insertNormal⟩
  rcases entryReply with ⟨entry, back⟩
  cases entry with
  | Occupied selected =>
    have lookedUp : PeerEntry views self.known_ids pending.peer.binding.assigned_key_id (.Occupied selected, back) := entryFootprint
    have normalized : AdapterPublicServerInstall.afterParse (m := m) self pending publicKey =
        pure (.None, { self with known_ids := back (.Occupied selected) }) := by
      unfold AdapterPublicServerInstall.afterParse
      rw [entryNormal, pure_bind]
    rw [normalized]
    refine ⟨.None, { self with known_ids := back (.Occupied selected) },
      AdapterPublicServerInstallNative.charged native pending, rfl,
      AdapterPublicServerInstallNative.occupied view views created credential self native related pending selected back lookedUp,
      ?_, ?_⟩
    · change Server view views created credential _ { AdapterPublicServerInstallNative.charged native pending with control := pending.previous }
      rw [previous]
      exact AdapterPublicServerInstallMaterial.entry view views created credential self
        (AdapterPublicServerInstallNative.charged native pending)
        (AdapterPublicServerInstallNative.charged_related view views created credential self native related pending)
        pending.peer.binding.assigned_key_id (.Occupied selected, back) lookedUp
    · intro response impossible
      cases impossible
  | Vacant selected =>
    have lookedUp : PeerEntry views self.known_ids pending.peer.binding.assigned_key_id (.Vacant selected, back) := entryFootprint
    obtain ⟨⟨changed, insertedBack⟩, inserted, updates⟩ := insertNormal selected back rfl
    have normalized : AdapterPublicServerInstall.afterParse (m := m) self pending publicKey =
        pure (.Some ⟨pending.encoded, pending.peer.binding.assigned_key_id⟩,
          { self with known_ids := back (.Vacant (insertedBack changed)), control := pending.next }) := by
      unfold AdapterPublicServerInstall.afterParse
      rw [entryNormal, pure_bind]
      dsimp only
      rw [inserted, pure_bind]
    rw [normalized]
    refine ⟨.Some ⟨pending.encoded, pending.peer.binding.assigned_key_id⟩,
      { self with known_ids := back (.Vacant (insertedBack changed)), control := pending.next },
      withPeer (AdapterPublicServerInstallNative.charged native pending) pending.peer.binding.assigned_key_id
        ⟨pending.peer.binding.beacon_identity_public_key, pending.peer.ratchet, pending.peer.binding.associated_data⟩,
      rfl, AdapterPublicServerInstallNative.vacant view views created credential self native related pending selected back lookedUp,
      ?_, ?_⟩
    · exact AdapterPublicServerInstallMaterial.vacant view views created credential self
        (AdapterPublicServerInstallNative.charged native pending)
        (AdapterPublicServerInstallNative.charged_related view views created credential self native related pending)
        pending publicKey back (changed, insertedBack) updates
    · intro response returned
      injection returned with same
      cases same
      exact ⟨rfl, rfl⟩
end BeaconcryptCore.Refinement.AdapterPublicServerInstallFunctional

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallFunctional.functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallFunctional.functional
