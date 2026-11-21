-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope
import BeaconcryptCore.Refinement.AdapterPublicWrapperStorage
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual source Server lookup and mutable-manager borrow follow individual standard-map lookup/lens contracts. Returning None to a borrowed present manager keeps that manager, exactly as the extracted source does. Every other map entry and all Server identity/control/replay fields remain unchanged. -/
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperStorage
open AdapterRecordRequestMonad (liftRust)
variable {m : Type →Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [ops : AdapterPublicOrdinaryRequestMonad.Operations (RustT m)]

def read (table : PeerMap) (key : U64) : RustT m (Option (Remote ed.PublicKey)) :=
  ops.get core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_wrapper.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) table key

def borrow (table : PeerMap) (key : U64) : RustT m (Option (Remote ed.PublicKey) ×(Option (Remote ed.PublicKey) →PeerMap)) :=
  ops.getMut core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_wrapper.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) table key

omit [LawfulMonad m] material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem lifted_ok {A : Type} (value : A) : (liftRust (.ok value) : RustT m A)=pure value := rfl

universe u v w
omit [Monad m] [LawfulMonad m] material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem call_apply {X : Type u} {F : X →Type v} {G : X →Type w}
    [∀x,AdapterPublicWrapperLiftFunction.LiftFunction (RustT m) (F x) (G x)]
    (source : (x : X) →F x) (value : X) :
    AdapterPublicWrapperLiftFunction.call (m:=RustT m) source value=
      AdapterPublicWrapperLiftFunction.call (m:=RustT m) (source value) := rfl
omit [LawfulMonad m] material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem call_result {A : Type} (source : RustM A) :
    AdapterPublicWrapperLiftFunction.call (m:=RustT m) source=(liftRust source :RustT m A) := rfl

omit [LawfulMonad m] material platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem binding (remote : Remote ed.PublicKey) :
    beaconcrypt_public_ordinary_request.shared.EstablishedRemote.binding (m:=RustT m)
      beaconcrypt_public_ordinary_request.beaconcrypt_crypto.crypto_sign.PublicKey.Insts.BeaconcryptSharedSignaturePk remote=pure remote.peer.binding := by
  rfl

omit material platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem remote_mut (remote : Remote ed.PublicKey) :
    beaconcrypt_public_ordinary_request.shared.EstablishedRemote.ratchet_mut (m:=RustT m)
      beaconcrypt_public_ordinary_request.beaconcrypt_crypto.crypto_sign.PublicKey.Insts.BeaconcryptSharedSignaturePk remote=
      pure (remote.peer.ratchet,fun manager=>{remote with peer:={remote.peer with ratchet:=manager}}) := by
  unfold beaconcrypt_public_ordinary_request.shared.EstablishedRemote.ratchet_mut
  simp only [call_apply,call_result,peer.Peer.ratchet_mut,lifted_ok,pure_bind]

theorem associated_data (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (get : read (m:=m) self.known_ids key=pure (views.peer self.known_ids key)) :
    beaconcrypt_public_ordinary_request.server.Server.associated_data (m:=RustT m) self key=
      pure ((views.peer self.known_ids key).map fun remote=>remote.peer.binding.associated_data) := by
  unfold read at get
  unfold beaconcrypt_public_ordinary_request.server.Server.associated_data
  rw [get,pure_bind]
  cases selected:views.peer self.known_ids key
  all_goals
    simp only [call_apply,call_result,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      binding,AdapterPublicOrdinaryPlatform.associatedData,lifted_ok,pure_bind]
  all_goals simp only [Option.map_none,Option.map_some]

omit [Monad m] [LawfulMonad m] ops in
def managerUpdate (selected : Option (Remote ed.PublicKey)) (changed : Option Manager) : Option (Remote ed.PublicKey) :=
  match selected with
  | none=>none
  | some remote=>some {remote with peer:={remote.peer with ratchet:=changed.getD remote.peer.ratchet}}

omit [Monad m] [LawfulMonad m] ops in
def restore (self : beaconcrypt_public_wrapper.server.Server) (selected : Option (Remote ed.PublicKey))
    (back : Option (Remote ed.PublicKey) →PeerMap) (changed : Option Manager) : beaconcrypt_public_wrapper.server.Server :=
  {self with known_ids:=back (managerUpdate selected changed)}

theorem manager_mut (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (selected : Option (Remote ed.PublicKey)) (back : Option (Remote ed.PublicKey) →PeerMap)
    (get : borrow (m:=m) self.known_ids key=pure (selected,back)) :
    beaconcrypt_public_ordinary_request.server.Server.ratchet_manager_mut (m:=RustT m) self key=
      pure (selected.map (fun remote=>remote.peer.ratchet),fun changed=>restore self selected back changed) := by
  unfold borrow at get
  unfold beaconcrypt_public_ordinary_request.server.Server.ratchet_manager_mut
  rw [get,pure_bind]
  cases selected with
  | none=>rfl
  | some remote=>
      dsimp only
      rw [remote_mut,pure_bind]
      apply congrArg (Pure.pure : (Option Manager ×(Option Manager →beaconcrypt_public_wrapper.server.Server)) →RustT m _)
      apply Prod.ext
      · simp only [Option.map_some]
      · funext changed
        cases changed <;>rfl

omit [Monad m] [LawfulMonad m] ops [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem restore_view (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (selected : Option (Remote ed.PublicKey)) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer self.known_ids query)
    (changed : Option Manager) (query : U64) :
    views.peer (restore self selected back changed).known_ids query=
      if query=key then managerUpdate selected changed else views.peer self.known_ids query := lens _ _

omit [Monad m] [LawfulMonad m] ops [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem restore_fields (self : beaconcrypt_public_wrapper.server.Server)
    (selected : Option (Remote ed.PublicKey)) (back : Option (Remote ed.PublicKey) →PeerMap) (changed : Option Manager) :
    (restore self selected back changed).identity=self.identity ∧
    (restore self selected back changed).control=self.control ∧
    (restore self selected back changed).consumed_registrations=self.consumed_registrations := ⟨rfl,rfl,rfl⟩
end BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.associated_data

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.manager_mut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.manager_mut

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.restore_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.restore_view

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.restore_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup.restore_fields
