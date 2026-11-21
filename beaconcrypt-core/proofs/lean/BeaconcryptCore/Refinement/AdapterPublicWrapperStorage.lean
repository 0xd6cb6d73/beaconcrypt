-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
import BeaconcryptCore.Computational.RawCtxServerRouting

/-! Actual owned peer/ratchet construction and narrow standard-container views for the selected public wrappers. Container contracts state membership, one-key insertion and mutable entry-lens footprints, never wrapper acceptance or protocol security. Reservations may change private allocation representation while preserving logical contents. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperStorage

abbrev Manager := beaconcrypt_public_wrapper.ratchet.RatchetManager
abbrev Remote (PublicKey : Type) := beaconcrypt_public_wrapper.shared.EstablishedRemote PublicKey

def peerView {PublicKey : Type} (remote : Remote PublicKey) :
    Option (BeaconcryptCore.Computational.RawCtxServerRouting.Peer (Std.Array U8 151#usize)) :=
  Option.map (fun kernel =>
    ⟨remote.peer.binding.beacon_identity_public_key, kernel, remote.peer.binding.associated_data⟩)
    remote.peer.ratchet.refined.kernel

theorem manager (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel kernel =
      .ok ⟨⟨.Some kernel⟩⟩ := rfl

theorem remote {PublicKey : Type} (signature : beaconcrypt_public_wrapper.shared.SignaturePk PublicKey)
    (publicKey : PublicKey) (peer : peer.Peer ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_wrapper.shared.EstablishedRemote.from_peer signature publicKey peer =
      .ok ⟨publicKey, ⟨peer.binding, ⟨⟨.Some peer.ratchet⟩⟩⟩⟩ := rfl

theorem remote_view {PublicKey : Type} (signature : beaconcrypt_public_wrapper.shared.SignaturePk PublicKey)
    (publicKey : PublicKey) (peer : peer.Peer ratchet.concrete.ConcreteRatchetKernel) :
    (do let stored ← beaconcrypt_public_wrapper.shared.EstablishedRemote.from_peer signature publicKey peer
        .ok (peerView stored)) =
      .ok (.some ⟨peer.binding.beacon_identity_public_key, peer.ratchet, peer.binding.associated_data⟩) := rfl

section Containers
open PublicWrapperPlatform
variable [platform : Platform] [ed : AdapterInitEdPrimitive.Operations]

abbrev PeerMap := hashbrown.map.HashMap U64 (Remote ed.PublicKey) platform.Hasher platform.Allocator
abbrev ReplaySet := hashbrown.set.HashSet (Std.Array U8 64#usize) platform.Hasher platform.Allocator
abbrev Occupied := hashbrown.map.OccupiedEntry U64 (Remote ed.PublicKey) platform.Hasher platform.Allocator
abbrev Vacant := hashbrown.map.VacantEntry U64 (Remote ed.PublicKey) platform.Hasher platform.Allocator
abbrev Entry := hashbrown.map.Entry U64 (Remote ed.PublicKey) platform.Hasher platform.Allocator

structure Views where
  peer : PeerMap → U64 → Option (Remote ed.PublicKey)
  replay : ReplaySet → Std.Array U8 64#usize → Bool

def ReplayRelated (views : Views) (stored : ReplaySet) (history : List Pqxdh.Bytes) : Prop :=
  ∀ identifier, views.replay stored identifier = true ↔ absBytes identifier ∈ history

def ReplayReserve (views : Views) (before : ReplaySet)
    (result : core.result.Result Unit platform.ReserveError × ReplaySet) : Prop :=
  ∀ identifier, views.replay result.2 identifier = views.replay before identifier

def ReplayInsert (views : Views) (before : ReplaySet) (identifier : Std.Array U8 64#usize)
    (result : Bool × ReplaySet) : Prop :=
  result.1 = !views.replay before identifier ∧
    ∀ query, views.replay result.2 query = true ↔ query = identifier ∨ views.replay before query = true

def PeerReserve (views : Views) (before : PeerMap)
    (result : core.result.Result Unit platform.ReserveError × PeerMap) : Prop :=
  ∀ identifier, views.peer result.2 identifier = views.peer before identifier

def PeerEntry (views : Views) (before : PeerMap) (identifier : U64)
    (result : Entry × (Entry → PeerMap)) : Prop :=
  (views.peer before identifier).isSome = (match result.1 with | .Occupied _ => true | .Vacant _ => false) ∧
    ∀ query, views.peer (result.2 result.1) query = views.peer before query

def VacantInsert (views : Views) (before : PeerMap) (identifier : U64) (back : Entry → PeerMap)
    (value : Remote ed.PublicKey) (result : Remote ed.PublicKey × (Remote ed.PublicKey → Vacant)) : Prop :=
  result.1 = value ∧ ∀ changed query,
    views.peer (back (.Vacant (result.2 changed))) query =
      if query = identifier then some changed else views.peer before query

def PeersRelated (views : Views) (stored : PeerMap)
    (native : U64 → Option (BeaconcryptCore.Computational.RawCtxServerRouting.Peer (Std.Array U8 151#usize))) : Prop :=
  ∀ identifier, Option.bind (views.peer stored identifier) peerView = native identifier ∧
    (views.peer stored identifier).isSome = (native identifier).isSome

theorem peer_reserve (views : Views) (before : PeerMap)
    (native : U64 → Option (BeaconcryptCore.Computational.RawCtxServerRouting.Peer (Std.Array U8 151#usize)))
    (result : core.result.Result Unit platform.ReserveError × PeerMap)
    (related : PeersRelated views before native) (preserves : PeerReserve views before result) :
    PeersRelated views result.2 native := by
  intro identifier
  rw [preserves identifier]
  exact related identifier

theorem vacant_absent (views : Views) (before : PeerMap)
    (native : U64 → Option (BeaconcryptCore.Computational.RawCtxServerRouting.Peer (Std.Array U8 151#usize)))
    (identifier : U64) (entry : Vacant) (back : Entry → PeerMap)
    (related : PeersRelated views before native) (lookedUp : PeerEntry views before identifier (.Vacant entry, back)) :
    native identifier = none := by
  have absent : (native identifier).isSome = false := (related identifier).2.symm.trans lookedUp.1
  cases value : native identifier with
  | none => rfl
  | some value =>
      have impossible : true = false := by simpa only [value, Option.isSome_some] using absent
      cases impossible

theorem peer_insert (views : Views) (before : PeerMap)
    (native : U64 → Option (BeaconcryptCore.Computational.RawCtxServerRouting.Peer (Std.Array U8 151#usize)))
    (identifier : U64) (back : Entry → PeerMap) (value : Remote ed.PublicKey)
    (result : Remote ed.PublicKey × (Remote ed.PublicKey → Vacant))
    (installed : BeaconcryptCore.Computational.RawCtxServerRouting.Peer (Std.Array U8 151#usize))
    (related : PeersRelated views before native) (updates : VacantInsert views before identifier back value result)
    (viewed : peerView value = some installed) :
    PeersRelated views (back (.Vacant (result.2 result.1))) (Function.update native identifier (some installed)) := by
  intro query
  rw [updates.2 result.1 query, updates.1]
  by_cases selected : query = identifier
  · subst query
    simp only [ite_true, Function.update_self, Option.bind_some, Option.isSome_some]
    exact ⟨viewed, trivial⟩
  · simp only [selected, ite_false, Function.update_of_ne selected]
    exact related query

theorem replay_reserve (views : Views) (before : ReplaySet) (history : List Pqxdh.Bytes)
    (result : core.result.Result Unit platform.ReserveError × ReplaySet)
    (related : ReplayRelated views before history) (preserves : ReplayReserve views before result) :
    ReplayRelated views result.2 history := by
  intro identifier
  rw [preserves identifier]
  exact related identifier

def inserted (history : List Pqxdh.Bytes) (identifier : Std.Array U8 64#usize) : List Pqxdh.Bytes :=
  if history.contains (absBytes identifier) then history else history ++ [absBytes identifier]

omit platform ed in
private theorem inserted_mem (history : List Pqxdh.Bytes) (identifier query : Std.Array U8 64#usize) :
    absBytes query ∈ inserted history identifier ↔ query = identifier ∨ absBytes query ∈ history := by
  unfold inserted
  split
  · have present : absBytes identifier ∈ history := by simpa using ‹history.contains (absBytes identifier) = true›
    constructor
    · exact Or.inr
    · rintro (rfl | member)
      · exact present
      · exact member
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (member | same)
      · exact Or.inr member
      · exact Or.inl (Subtype.ext ((absBytes_inj_iff query identifier).mp same))
    · rintro (rfl | member)
      · exact Or.inr rfl
      · exact Or.inl member

theorem replay_insert (views : Views) (before : ReplaySet) (history : List Pqxdh.Bytes)
    (identifier : Std.Array U8 64#usize) (result : Bool × ReplaySet)
    (related : ReplayRelated views before history) (updates : ReplayInsert views before identifier result) :
    ReplayRelated views result.2 (inserted history identifier) := by
  intro query
  exact (updates.2 query).trans ((or_congr Iff.rfl (related query)).trans (inserted_mem history identifier query).symm)

end Containers
end BeaconcryptCore.Refinement.AdapterPublicWrapperStorage

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.manager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.manager

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.remote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.remote

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.remote_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.remote_view

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.peer_reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.peer_reserve

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.vacant_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.vacant_absent

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.peer_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.peer_insert

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.replay_reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.replay_reserve

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.replay_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.replay_insert
