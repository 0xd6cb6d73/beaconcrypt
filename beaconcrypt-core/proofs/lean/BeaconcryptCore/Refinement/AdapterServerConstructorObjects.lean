-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The source constructor's actual keyed empty stores and shared identity use individual standard-library leaf contracts. These contracts expose no constructor, protocol-state or security conclusion. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorObjects
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [standard : AdapterServerConstructorPrimitive.Standard]

structure Leaves (views : Views) where
  bytes : beaconcrypt_crypto.crypto_sign.SecretKey → Array U8 64#usize
  known : Slice U8 → PeerMap
  replay : Slice U8 → ReplaySet
  shared : beaconcrypt_public_wrapper.server.ServerIdentity → platform.Arc beaconcrypt_public_wrapper.server.ServerIdentity
  bytes_source : ∀ secret,standard.edSecretBytes secret=.ok (bytes secret)
  known_source : ∀ key,standard.mapWithKey U64
    (beaconcrypt_public_wrapper.shared.EstablishedRemote beaconcrypt_crypto.crypto_sign.PublicKey) key=.ok (known key)
  replay_source : ∀ key,standard.setWithKey (Array U8 64#usize) key=.ok (replay key)
  shared_source : ∀ identity,standard.arcNew identity=.ok (shared identity)
  shared_view : ∀ identity,platform.arcView (shared identity)=identity
  known_empty : ∀ key identifier,views.peer (known key) identifier=none
  replay_empty : ∀ key identifier,views.replay (replay key) identifier=false

variable {m : Type → Type} [Monad m] [LawfulMonad m]
omit material platform primitive standard [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A)=pure value := rfl


def stored (views : Views) (leaves : Leaves views) (identifier : U64)
    (signing : beaconcrypt_crypto.crypto_sign.KeyPair) (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) :
    beaconcrypt_public_wrapper.server.Server :=
  let key := (leaves.bytes signing.secret_key).to_slice
  ⟨leaves.shared ⟨signing,identity,identifier⟩,⟨identifier⟩,leaves.known key,leaves.replay key⟩

theorem assemble (views : Views) (leaves : Leaves views) (identifier : U64)
    (signing : beaconcrypt_crypto.crypto_sign.KeyPair) (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) :
    AdapterServerConstructorBody.assemble (m:=m) identifier signing identity=pure (stored views leaves identifier signing identity) := by
  unfold AdapterServerConstructorBody.assemble
  rw [leaves.bytes_source]
  change (do
    let bytes ← (pure (leaves.bytes signing.secret_key) : RustT m _)
    let slice ← pure bytes.to_slice
    let known ← AdapterRecordRequestMonad.liftRust (standard.mapWithKey U64
      (beaconcrypt_public_wrapper.shared.EstablishedRemote beaconcrypt_crypto.crypto_sign.PublicKey) slice)
    let slice ← pure bytes.to_slice
    let consumed ← AdapterRecordRequestMonad.liftRust (standard.setWithKey (Array U8 64#usize) slice)
    let shared ← AdapterRecordRequestMonad.liftRust (standard.arcNew (⟨signing,identity,identifier⟩ : beaconcrypt_public_wrapper.server.ServerIdentity))
    let control ← pure (pqxdh.ServerState.mk identifier)
    pure (beaconcrypt_public_wrapper.server.Server.mk shared control known consumed)) = _
  simp only [pure_bind,leaves.known_source,leaves.replay_source,leaves.shared_source,lift_ok]
  rfl

omit m [Monad m] [LawfulMonad m] in
theorem identity {source : RegistrationNativeMldsa.Source} {KemSK : Type}
    (view : MaterialView source KemSK) (views : Views) (leaves : Leaves views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (signing : beaconcrypt_crypto.crypto_sign.KeyPair) (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity)
    (edPublic : view.edPublic signing.public_key=created.server.server.identity)
    (edPrivate : view.edSecret signing.secret_key=created.seed)
    (mlPrivate : view.mldsa identity=credential) :
    ServerIdentity view (platform.arcView (stored views leaves created.server.server.metadata.sender signing identity).identity) created credential := by
  dsimp only [stored]
  rw [leaves.shared_view]
  exact ⟨edPublic,edPrivate,mlPrivate,rfl⟩

omit m [Monad m] [LawfulMonad m] in
theorem empty (views : Views) (leaves : Leaves views) (identifier : U64)
    (signing : beaconcrypt_crypto.crypto_sign.KeyPair) (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) :
    ReplayRelated views (stored views leaves identifier signing identity).consumed_registrations [] ∧
    PeersRelated views (stored views leaves identifier signing identity).known_ids (fun _=>none) := by
  constructor
  · intro query
    simp only [stored,leaves.replay_empty,Bool.false_eq_true,List.not_mem_nil,iff_self]
  · intro query
    simp only [stored,leaves.known_empty,Option.bind_none,Option.isSome_none,and_self]
end BeaconcryptCore.Refinement.AdapterServerConstructorObjects

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorObjects.assemble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorObjects.assemble

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorObjects.identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorObjects.identity

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorObjects.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorObjects.empty
