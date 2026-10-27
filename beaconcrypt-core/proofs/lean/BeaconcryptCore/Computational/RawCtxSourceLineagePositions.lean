import BeaconcryptCore.Computational.RawCtxLiveLineage
import BeaconcryptCore.Computational.RawCtxRevealPositions

/-!
Finite private lineage follows the source's logical record positions. Iterating the next-chain handle interprets exactly as the fixed-source chain at that position, and its material is the record key and nonce at that same position. Earlier current-chain disclosures therefore invalidate descendants through the actual optional source reply and retained history; successful skipped-key disclosures invalidate their exact record. These are source exposure and freshness facts, not independent-key assumptions or secrecy claims. The position invariant is the existing operational relation, supplied at initialization and preserved by the complete adaptive source schedule. No snapshot or persistence operation is modeled.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceLineagePositions
open RawCtxSourceChainHandles RawCtxLiveLineage RawCtxRevealPositions
open RawCtxPositionedOwner RawCtxProtocolPositions RawCtxProtocolReveals
variable {Atom : Type}

/-- Position zero is the supplied directional initial chain; one step follows the source second32 output. -/
def inputAt (origin : Chain Atom) : Nat → Chain Atom
  | 0 => origin
  | position + 1 => .next (inputAt origin position)

/-- Private next-chain provenance interprets to exactly the source chain at the same logical position. -/
theorem chain_position
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (origin : Chain Atom) (position : Nat) :
    chainOf source roots (inputAt origin position) =
      Ratchet.chainAt (crypto source.crypto) (chainOf source roots origin) position := by
  induction position with
  | zero => rfl
  | succ position ih =>
    simp only [inputAt, chainOf, ih, Ratchet.chainAt, Function.iterate_succ_apply']
    rfl

/-- The record material at a private input handle is the same full key and nonce at its source position. -/
theorem material_position
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (origin : Chain Atom) (position : Nat) :
    materialOf source roots (inputAt origin position) =
      Ratchet.msgKeyAt (crypto source.crypto) (chainOf source roots origin) position := by
  simp only [materialOf, chain_position, Ratchet.msgKeyAt]
  rfl

/-- Every earlier directional input occurs in the selected record's finite source lineage, with no distinctness assumption on its interpreted bytes. -/
theorem earlier_mem (origin : Chain Atom) (earlier position : Nat) (before : earlier ≤ position) :
    inputAt origin earlier ∈ lineage (inputAt origin position) := by
  induction position with
  | zero => simpa only [Nat.le_zero.mp before, inputAt] using self_mem origin
  | succ position ih =>
    rcases Nat.eq_or_lt_of_le before with same | less
    · subst earlier
      exact self_mem _
    · exact List.mem_cons_of_mem _ (ih (Nat.le_of_lt_succ less))

/-- An actual source chain at any earlier index is a forbidden disclosure for the selected record. -/
theorem earlier_forbidden
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (origin : Chain Atom) (earlier position : Nat) (before : earlier ≤ position) :
    Ratchet.chainAt (crypto source.crypto) (chainOf source roots origin) earlier ∈
      forbidden source roots (inputAt origin position) := by
  rw [← chain_position]
  exact ancestor_forbidden source roots _ _ (earlier_mem origin earlier position before)

/-- An actual successful current-chain reply rules out freshness for every later record on the same source direction; no post-compromise recovery is inferred from erasing or advancing that chain. -/
theorem current_descendant_not_fresh {M P I D K : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (origin : Chain Atom) (serverOrigins : Fin S → Std.U64 → Origins) (beaconOrigins : Fin B → Origins)
    (roles : Roles M P I D K S B)
    (invariant : RolesPositioned source.crypto serverOrigins beaconOrigins roles)
    (owner : Owner S B) (kernel : ConcreteRatchetKernel) (selected : selectedKernel owner roles = some kernel)
    (direction : Direction) (sameOrigin : chainOrigin (ownerOrigins serverOrigins beaconOrigins owner) direction =
      chainOf source roots origin) (chain : RatchetChain)
    (returned : chainReveal owner direction roles = .Some chain)
    (position : Nat) (later : chainIndex kernel direction ≤ position)
    (prior : List RatchetChain) (history : History S B) (retained : chain ∈ known prior history) :
    ¬ Fresh (forbidden source roots (inputAt origin position)) prior history := by
  have actual := chain_disclosure_index source.crypto serverOrigins beaconOrigins roles invariant owner kernel selected
    direction chain returned
  rw [sameOrigin] at actual
  exact fun fresh => fresh chain (actual ▸ earlier_forbidden source roots origin _ position later) retained

/-- A successful source skipped-key read identifies a positive wire sequence and invalidates that exact record when its actual reply is appended to the history. -/
theorem skipped_record_not_fresh {M P I D K : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (roots : Atom → RatchetChain)
    (origin : Chain Atom) (serverOrigins : Fin S → Std.U64 → Origins) (beaconOrigins : Fin B → Origins)
    (roles : Roles M P I D K S B)
    (invariant : RolesPositioned source.crypto serverOrigins beaconOrigins roles)
    (owner : Owner S B) (kernel : ConcreteRatchetKernel) (selected : selectedKernel owner roles = some kernel)
    (sameOrigin : (ownerOrigins serverOrigins beaconOrigins owner).2 = chainOf source roots origin)
    (sequence : Std.U64) (material : RatchetMaterial)
    (returned : reveal (.skippedKey owner sequence) roles = .Some material)
    (prior : List RatchetChain) (history : History S B) :
    0 < sequence.val ∧ ¬ Fresh (forbidden source roots (inputAt origin (sequence.val - 1))) prior
      (note ⟨.skippedKey owner sequence, .Some material⟩ history) := by
  obtain ⟨positive, actual⟩ := skipped_reveal_positions source.crypto serverOrigins beaconOrigins roles invariant
    owner kernel selected sequence material returned
  rw [sameOrigin, ← material_position] at actual
  refine ⟨positive, known_material_not_fresh source roots _ _ ?_⟩
  simp [known, note, disclosed, actual]

end BeaconcryptCore.Computational.RawCtxSourceLineagePositions

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceLineagePositions.chain_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceLineagePositions.chain_position
/-- info: 'BeaconcryptCore.Computational.RawCtxSourceLineagePositions.material_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceLineagePositions.material_position
/-- info: 'BeaconcryptCore.Computational.RawCtxSourceLineagePositions.earlier_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceLineagePositions.earlier_mem
/-- info: 'BeaconcryptCore.Computational.RawCtxSourceLineagePositions.earlier_forbidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceLineagePositions.earlier_forbidden
/-- info: 'BeaconcryptCore.Computational.RawCtxSourceLineagePositions.current_descendant_not_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceLineagePositions.current_descendant_not_fresh
/-- info: 'BeaconcryptCore.Computational.RawCtxSourceLineagePositions.skipped_record_not_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceLineagePositions.skipped_record_not_fresh
