-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction

/-!
Functional collection semantics for the peer-publication interpreter. The collection implementation remains external: its membership and vacant-entry operations must satisfy the explicit laws below. These laws do not assert correctness of Rust's HashMap or HashSet implementations.
-/

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.PeerCollections

/-- The extensional observation of a peer collection, including every unselected peer. -/
abbrev PeerMap (Peer : Type) := Nat → Option Peer

/-- Publishing a fresh peer replaces exactly its selected map entry. -/
def publishAt {Peer : Type} (before : PeerMap Peer) (key : Nat) (peer : Peer) : PeerMap Peer :=
  fun selected => if selected = key then some peer else before selected

/-- The selected entry contains the actual published peer. -/
theorem publishAt_selected {Peer : Type} (before : PeerMap Peer) (key : Nat) (peer : Peer) :
    publishAt before key peer key = some peer := by
  simp [publishAt]

/-- Publication leaves every unselected peer unchanged. -/
theorem publishAt_other {Peer : Type} (before : PeerMap Peer) (key selected : Nat) (peer : Peer)
    (different : selected ≠ key) :
    publishAt before key peer selected = before selected := by
  simp [publishAt, different]

/-- Laws required of the native vacant-entry operation and its actual Boolean reply. The peer argument is the peer yielded by the core publication capability. -/
structure FaithfulFreshInsert {Peer : Type} (before : PeerMap Peer) (key : Nat) (peer : Peer)
    (inserted : Bool) (after : PeerMap Peer) : Prop where
  vacant : inserted = true ↔ before key = none
  selected : inserted = true → after key = some peer
  other : ∀ selected, selected ≠ key → after selected = before selected
  failed : inserted = false → after = before

/-- Faithful successful insertion is exactly the one-entry update, with freshness derived from the insertion reply. -/
theorem faithful_success {Peer : Type} (before : PeerMap Peer) (key : Nat) (peer : Peer)
    (inserted : Bool) (after : PeerMap Peer)
    (faithful : FaithfulFreshInsert before key peer inserted after) (success : inserted = true) :
    before key = none ∧ after = publishAt before key peer := by
  refine ⟨faithful.vacant.mp success, funext fun selected => ?_⟩
  by_cases same : selected = key
  · subst selected
    exact (faithful.selected success).trans (publishAt_selected before key peer).symm
  · exact (faithful.other selected same).trans (publishAt_other before key selected peer same).symm

/-- A rejected insertion preserves the complete peer map and proves the selected entry was occupied. -/
theorem faithful_failure {Peer : Type} (before : PeerMap Peer) (key : Nat) (peer : Peer)
    (after : PeerMap Peer) (faithful : FaithfulFreshInsert before key peer false after) :
    before key ≠ none ∧ after = before := by
  exact ⟨fun free => Bool.noConfusion (faithful.vacant.mpr free), faithful.failed rfl⟩

/-- An occupied entry can never be replaced by the publication interpreter. -/
theorem faithful_no_replacement {Peer : Type} (before : PeerMap Peer) (key : Nat)
    (old peer : Peer) (inserted : Bool) (after : PeerMap Peer)
    (faithful : FaithfulFreshInsert before key peer inserted after) (occupied : before key = some old) :
    after key = some old := by
  cases inserted
  · exact congrFun (faithful.failed rfl) key |>.trans occupied
  · nomatch (faithful.vacant.mp rfl).symm.trans occupied

/-- The extensional observation of consumed registration identifiers. -/
abbrev ReplaySet := List UInt8 → Bool

/-- A replay insertion monotonically consumes its exact selected identifier. -/
def consumeAt (before : ReplaySet) (identifier : List UInt8) : ReplaySet :=
  fun selected => if selected = identifier then true else before selected

/-- The consumed identifier is present independently of its previous membership. -/
theorem consumeAt_selected (before : ReplaySet) (identifier : List UInt8) :
    consumeAt before identifier identifier = true := by
  simp [consumeAt]

/-- Consuming one identifier preserves every other identifier's membership. -/
theorem consumeAt_other (before : ReplaySet) (identifier selected : List UInt8)
    (different : selected ≠ identifier) :
    consumeAt before identifier selected = before selected := by
  simp [consumeAt, different]

/-- Replay consumption cannot remove any previously consumed identifier. -/
theorem consumeAt_monotone (before : ReplaySet) (identifier selected : List UInt8)
    (present : before selected = true) :
    consumeAt before identifier selected = true := by
  simp [consumeAt, present]

/-- Reconsuming an identifier has no further set effect. -/
theorem consumeAt_idempotent (before : ReplaySet) (identifier : List UInt8) :
    consumeAt (consumeAt before identifier) identifier = consumeAt before identifier := by
  funext selected
  simp [consumeAt]

/-- Membership and insertion laws required of the native replay-set interpreter. -/
structure FaithfulReplayInsert (before : ReplaySet) (identifier : List UInt8)
    (inserted : Bool) (after : ReplaySet) : Prop where
  reply : inserted = !before identifier
  selected : after identifier = true
  other : ∀ selected, selected ≠ identifier → after selected = before selected

/-- The faithful replay operation has exactly the complete functional set effect. -/
theorem faithful_replay_effect (before : ReplaySet) (identifier : List UInt8)
    (inserted : Bool) (after : ReplaySet)
    (faithful : FaithfulReplayInsert before identifier inserted after) :
    after = consumeAt before identifier := by
  apply funext
  intro selected
  by_cases same : selected = identifier
  · simpa [consumeAt, same] using faithful.selected
  · simpa [consumeAt, same] using faithful.other selected same

end BeaconcryptCore.Refinement.PeerCollections

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.publishAt_selected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.publishAt_selected

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.publishAt_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.publishAt_other

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.faithful_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.faithful_success

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.faithful_failure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.faithful_failure

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.faithful_no_replacement' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.faithful_no_replacement

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.consumeAt_selected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.consumeAt_selected

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.consumeAt_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.consumeAt_other

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.consumeAt_monotone' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.consumeAt_monotone

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.consumeAt_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.consumeAt_idempotent

/-- info: 'BeaconcryptCore.Refinement.PeerCollections.faithful_replay_effect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.PeerCollections.faithful_replay_effect
