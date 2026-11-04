-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildBody
import BeaconcryptCore.Refinement.AdapterPublicServerToken
import BeaconcryptCore.Refinement.PeerOwnership
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual Server installer consumes an earlier source parse receipt. It retains the exact map-entry lens, occupied rejection, vacant insertion and full source object/kernel/control updates. This local source equality does not assert that arbitrary caller-created tokens carry that receipt. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerInstall
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
open AdapterPublicWrapperLiftFunction (LiftFunction call)
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem call_result {m : Type → Type} [AdapterRecordRequestMonad.LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [containers : ContainerOperations (RustT m)]

noncomputable def entry (stored : PeerMap) (identifier : U64) : RustT m (Entry × (Entry → PeerMap)) :=
  containers.mapEntry core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator stored identifier

noncomputable def insert (vacant : Vacant) (value : Remote ed.PublicKey) :
    RustT m (Remote ed.PublicKey × (Remote ed.PublicKey → Vacant)) :=
  containers.vacantInsert hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13 vacant value

omit containers in
def remote (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey) : Remote ed.PublicKey :=
  ⟨publicKey, ⟨pending.peer.binding, ⟨⟨.Some pending.peer.ratchet⟩⟩⟩⟩

omit containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] material platform in
theorem remote_source (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey) :
    beaconcrypt_public_request.shared.EstablishedRemote.from_peer
      (m := RustT m) beaconcrypt_public_request.beaconcrypt_crypto.crypto_sign.PublicKey.Insts.BeaconcryptSharedSignaturePk
      publicKey pending.peer = pure (remote pending publicKey) := by
  simp only [beaconcrypt_public_request.shared.EstablishedRemote.from_peer,
    beaconcrypt_public_request.shared.map_peer_ratchet,
    beaconcrypt_public_request.ratchet.RatchetManager.from_kernel,
    beaconcrypt_public_request.ratchet.RatchetKernelSlot.new,
    call_apply, call_result, peer.Peer.into_parts, peer.Peer.from_trusted_parts, lift_ok, pure_bind]
  rfl

omit containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem finish (self : beaconcrypt_public_wrapper.server.Server)
    (completion : peer.PublicationFinish (alloc.vec.Vec U8)) (inserted : Bool) :
    AdapterPublicServerBuildBody.finish (m := m) self completion inserted =
      pure (if inserted then
        (.Some ⟨completion.encoded, completion.key_id⟩, { self with control := completion.next })
        else (.None, self)) := by
  cases inserted <;>
    simp only [AdapterPublicServerBuildBody.finish, AdapterPublicServerBuildBody.checked,
      PeerOwnership.publication_finish, Bool.false_eq_true, ↓reduceIte,
      PeerOwnership.published_peer_parts, lift_ok, pure_bind]

noncomputable def afterParse (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey) :
    RustT m AdapterPublicServerBuildBody.Reply := do
  let (lookedUp, back) ← entry self.known_ids pending.peer.binding.assigned_key_id
  match lookedUp with
  | .Occupied _ => pure (.None, { self with known_ids := back lookedUp })
  | .Vacant vacant =>
    let (changed, insertedBack) ← insert vacant (remote pending publicKey)
    pure (.Some ⟨pending.encoded, pending.peer.binding.assigned_key_id⟩,
      { self with known_ids := back (.Vacant (insertedBack changed)), control := pending.next })

theorem install (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey)) :
    AdapterPublicServerBuildBody.install (m := m) self pending = afterParse self pending publicKey := by
  simp only [AdapterPublicServerBuildBody.install, PeerOwnership.peer_insert_request,
    PeerOwnership.peer_insert_parts, PublicWrapperPlatform.peerBinding, PublicWrapperPlatform.beaconIdentity,
    lift_ok, pure_bind, parsed,
    AdapterPublicServerBuildBody.checked]
  unfold afterParse entry
  apply bind_congr
  rintro ⟨lookedUp, back⟩
  cases lookedUp with
  | Occupied occupied => rw [finish]; rfl
  | Vacant vacant =>
    rw [remote_source]
    change (do
      let stored ← pure (remote pending publicKey)
      let (changed, insertedBack) ← insert vacant stored
      AdapterPublicServerBuildBody.finish (m := m)
        { self with known_ids := back (.Vacant (insertedBack changed)) }
        ⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ true) = _
    rw [pure_bind]
    apply bind_congr
    rintro ⟨changed, insertedBack⟩
    dsimp only
    rw [finish]
    rfl

omit containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [Monad m] [LawfulMonad m] material platform in
theorem remote_view (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey) :
    peerView (remote pending publicKey) = some
      ⟨pending.peer.binding.beacon_identity_public_key, pending.peer.ratchet, pending.peer.binding.associated_data⟩ := rfl
end BeaconcryptCore.Refinement.AdapterPublicServerInstall

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstall.remote_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstall.remote_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstall.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstall.finish

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstall.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstall.install

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstall.remote_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstall.remote_view
