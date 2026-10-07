-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle

/-! Finite topological ordering of actual hidden-chain coordinates. The predicates select only private labeled callbacks; complete global reachability and cryptographic hop simulation remain separate obligations. -/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable

variable {n positions : Nat}

def directionIndex : Bool ≃ Fin 2 where
  toFun direction := if direction then 1 else 0
  invFun index := decide (index.val = 1)
  left_inv direction := by cases direction <;> rfl
  right_inv index := by fin_cases index <;> rfl

/-- Depth precedes slot and direction, so every predecessor belongs to an earlier block. -/
abbrev Cell (n positions : Nat) := Fin positions × (Fin n × Bool)

def ordering : Cell n positions ≃ Fin (positions * (n * 2)) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) directionIndex).trans
    finProdFinEquiv)).trans finProdFinEquiv

def coordinate (cell : Cell n positions) : Coordinate (Fin n) :=
  ⟨cell.2.1, cell.2.2, start cell.2.2 + cell.1.val⟩

def Bounded (positions : Nat) (entry : Coordinate (Fin n)) : Prop :=
  start entry.direction ≤ entry.position ∧ entry.position < start entry.direction + positions

def cellOf (entry : Coordinate (Fin n)) (bounded : Bounded positions entry) : Cell n positions :=
  (⟨entry.position - start entry.direction, by rcases bounded with ⟨_, _⟩; omega⟩,
    entry.slot, entry.direction)

/-- A bounded source coordinate is recovered without comparing any cryptographic bytes. -/
theorem coordinate_cellOf (entry : Coordinate (Fin n)) (bounded : Bounded positions entry) :
    coordinate (cellOf entry bounded) = entry := by
  cases entry; simp only [coordinate, cellOf, Coordinate.mk.injEq, true_and]
  exact Nat.add_sub_of_le bounded.1

/-- The finite enumeration contains precisely the direction-relative source depths below the stated cap. -/
theorem coordinate_bounded (cell : Cell n positions) :
    Bounded positions (coordinate cell) := by
  simp only [Bounded, coordinate]; omega

/-- Enumerating and then reading a coordinate keeps its exact depth, slot and direction. -/
theorem cellOf_coordinate (cell : Cell n positions) :
    cellOf (coordinate cell) (coordinate_bounded cell) = cell := by
  simp [coordinate, cellOf]

def index (entry : Coordinate (Fin n)) (bounded : Bounded positions entry) :
    Fin (positions * (n * 2)) := ordering (cellOf entry bounded)

def entryAt (step : Fin (positions * (n * 2))) : Coordinate (Fin n) :=
  coordinate (ordering.symm step)

/-- The selected index decodes to exactly the original bounded source coordinate. -/
theorem at_index (entry : Coordinate (Fin n)) (bounded : Bounded positions entry) :
    entryAt (index entry bounded) = entry := by
  simp only [entryAt, index, Equiv.symm_apply_apply, coordinate_cellOf]

/-- Every index has a bounded coordinate, including the two different directional starts. -/
theorem at_bounded (step : Fin (positions * (n * 2))) : Bounded positions (entryAt step) :=
  coordinate_bounded _

/-- No two finite hops are aliases of the same logical coordinate. Byte equality is unrelated. -/
theorem index_at (step : Fin (positions * (n * 2))) :
    index (entryAt step) (at_bounded step) = step := by
  simp only [index, entryAt, cellOf_coordinate, Equiv.apply_symm_apply]

/-- Equality of logical indices determines the complete coordinate, without a key-injectivity premise. -/
theorem index_injective (left right : Coordinate (Fin n))
    (hleft : Bounded positions left) (hright : Bounded positions right)
    (same : index left hleft = index right hright) : left = right :=
  (at_index left hleft).symm.trans ((congrArg entryAt same).trans (at_index right hright))

noncomputable def selected (positions cut : Nat) (entry : Coordinate (Fin n)) : Bool := by
  classical
  exact decide (∃ bounded : Bounded positions entry, (index entry bounded).val < cut)

/-- Before the first replacement every actual callback is real. -/
theorem selected_zero (entry : Coordinate (Fin n)) : selected positions 0 entry = false := by
  simp [selected]

/-- After all finite replacements every in-range coordinate is ideal; values outside the range stay real. -/
theorem selected_last (entry : Coordinate (Fin n)) :
    selected positions (positions * (n * 2)) entry = true ↔ Bounded positions entry := by
  simp only [selected, decide_eq_true_eq]
  exact ⟨fun ⟨bounded, _⟩ => bounded, fun bounded => ⟨bounded, (index entry bounded).isLt⟩⟩

/-- On every in-range callback the mode is exactly the comparison with its unique logical index. -/
theorem selected_bounded (entry : Coordinate (Fin n)) (bounded : Bounded positions entry) (cut : Nat) :
    selected positions cut entry = decide ((index entry bounded).val < cut) := by
  simp [selected, bounded]

/-- Advancing one hybrid changes no other logical callback, regardless of aliases among its bytes. -/
theorem selected_unchanged (step : Fin (positions * (n * 2))) (entry : Coordinate (Fin n))
    (different : entry ≠ entryAt step) :
    selected positions (step.val + 1) entry = selected positions step.val entry := by
  classical
  by_cases bounded : Bounded positions entry
  · rw [selected_bounded entry bounded, selected_bounded entry bounded]
    have unequal : index entry bounded ≠ step := fun equal => different ((at_index entry bounded).symm.trans (congrArg entryAt equal))
    have : (index entry bounded).val ≠ step.val := fun equal => unequal (Fin.ext equal)
    exact decide_eq_decide.mpr (by omega)
  · simp [selected, bounded]

/-- The unique chosen callback changes from real to ideal at this exact finite step. -/
theorem selected_step (step : Fin (positions * (n * 2))) :
    selected positions step.val (entryAt step) = false ∧
      selected positions (step.val + 1) (entryAt step) = true := by
  simp only [selected_bounded _ (at_bounded step), index_at, lt_self_iff_false,
    decide_false, Nat.lt_succ_self, decide_true, and_self]

/-- Exact index arithmetic exposes the depth-major ordering and its two-direction count. -/
theorem index_value (entry : Coordinate (Fin n)) (bounded : Bounded positions entry) :
    (index entry bounded).val = (if entry.direction then 1 else 0) + 2 * entry.slot.val +
      (n * 2) * (entry.position - start entry.direction) := by
  cases direction : entry.direction <;> simp [index, ordering, cellOf, directionIndex, direction]

/-- Advancing one source derivation moves by exactly one whole slot/direction block. -/
theorem index_advance (entry : Coordinate (Fin n)) (bounded : Bounded positions entry)
    (nextBounded : Bounded positions (advance entry 1)) :
    (index (advance entry 1) nextBounded).val = (index entry bounded).val + n * 2 := by
  rw [index_value, index_value]
  have offset : entry.position + 1 - start entry.direction = entry.position - start entry.direction + 1 := by
    have lower := bounded.1
    omega
  simp only [advance, offset, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  rfl

/-- Every ordinary successor is replaced after its predecessor, not simultaneously with it. -/
theorem index_advance_lt (entry : Coordinate (Fin n)) (bounded : Bounded positions entry)
    (nextBounded : Bounded positions (advance entry 1)) :
    (index entry bounded).val < (index (advance entry 1) nextBounded).val := by
  rw [index_advance entry bounded nextBounded]
  have positive := entry.slot.isLt
  omega

/-- A callback reads its own mode only; every output byte, cache entry and native counter remains in this equality. -/
theorem lookup_agrees {Slot : Type} [DecidableEq Slot]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (left right : Coordinate Slot → Bool) (entry : Coordinate Slot) (same : left entry = right entry) :
    PqxdhRecordLiftChainOracle.lookup source seeds left entry =
      PqxdhRecordLiftChainOracle.lookup source seeds right entry := by
  funext state
  simp only [PqxdhRecordLiftChainOracle.lookup, same]

/-- Adjacent replacements are the exact same complete callback away from their single selected coordinate. -/
theorem lookup_adjacent (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (step : Fin (positions * (n * 2))) (entry : Coordinate (Fin n))
    (different : entry ≠ entryAt step) :
    PqxdhRecordLiftChainOracle.lookup source seeds (selected positions (step.val + 1)) entry =
      PqxdhRecordLiftChainOracle.lookup source seeds (selected positions step.val) entry :=
  lookup_agrees source seeds _ _ entry (selected_unchanged step entry different)

/-- A larger executed-call cap contains every previously bounded source coordinate. -/
theorem bounded_mono (entry : Coordinate (Fin n)) {before after : Nat}
    (bounded : Bounded before entry) (larger : before ≤ after) : Bounded after entry := by
  unfold Bounded at *
  omega

/-- Every populated depth has already been justified by the actual executed native KDF count. -/
def DepthBound (table : Table (Fin n)) (calls : Nat) : Prop :=
  ∀ entry value, table entry = some value → Bounded calls entry

/-- The next available callback is below the post-call cap even when previous failed work is retained. -/
theorem available_bounded (table : Table (Fin n)) (calls : Nat) (bounded : DepthBound table calls)
    (entry : Coordinate (Fin n)) (available : Available table entry) : Bounded (calls + 1) entry := by
  rcases available with initial | ⟨later, value, found⟩
  · simp [Bounded, initial]
  · have prior := bounded _ value found
    simp only [Bounded, previous] at prior ⊢
    omega

/-- Recording an available request preserves the depth bound at the actual next callback count. -/
theorem depth_record (table : Table (Fin n)) (calls : Nat) (bounded : DepthBound table calls)
    (entry : Coordinate (Fin n)) (available : Available table entry)
    (value : PqxdhFullSecretInputKdf.FullOutput) :
    DepthBound (table.cacheQuery entry value) (calls + 1) := by
  intro other output found
  by_cases same : other = entry
  · subst other
    exact available_bounded table calls bounded entry available
  · exact bounded_mono other (bounded other output
      ((QueryCache.cacheQuery_of_ne table value same).symm.trans found)) (Nat.le_succ calls)

/-- Initialization justifies no invented depth and needs no pre-sampled seed family. -/
theorem depth_empty : DepthBound (∅ : Table (Fin n)) 0 := by
  simp [DepthBound]

/-- Work elsewhere can increase the executed counter while retaining the same table. -/
theorem depth_mono (table : Table (Fin n)) {before after : Nat}
    (bounded : DepthBound table before) (larger : before ≤ after) : DepthBound table after :=
  fun entry value found => bounded_mono entry (bounded entry value found) larger

/-- The concrete real/mixed callback derives the finite-depth bound from its actual native KDF charge. Repeats and ideal hits still pay one callback. -/
theorem lookup_depth (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool) (entry : Coordinate (Fin n))
    (state : PqxdhRecordLiftChainCompiler.Execution (Fin n) PqxdhRecordLiftWorld.Primitive)
    (bounded : DepthBound state.1 (state.2.1.native .kdf)) (available : Available state.1 entry)
    (result : PqxdhFullSecretInputKdf.FullOutput ×
      PqxdhRecordLiftChainCompiler.Execution (Fin n) PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftChainOracle.lookup source seeds ideal entry).run state)) :
    DepthBound result.2.1 (result.2.2.1.native .kdf) := by
  cases mode : ideal entry with
  | false =>
    rw [PqxdhRecordLiftChainOracle.lookup_real source seeds ideal entry state mode,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact depth_record state.1 _ bounded entry available _
  | true =>
    cases found : state.1 entry with
    | some value =>
      rw [PqxdhRecordLiftChainOracle.lookup_hit source seeds ideal entry state mode value found,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact depth_mono state.1 bounded (Nat.le_succ _)
    | none =>
      rw [PqxdhRecordLiftChainOracle.lookup_miss source seeds ideal entry state mode found,
        support_map] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact depth_record state.1 _ bounded entry available value

/-- The first ordered callback interpreter is literally the all-real interpreter. -/
theorem lookup_initial (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) :
    PqxdhRecordLiftChainOracle.lookup source seeds (selected positions 0) =
      PqxdhRecordLiftChainOracle.lookup source seeds (fun _ => false) :=
  congrArg (PqxdhRecordLiftChainOracle.lookup source seeds) (funext selected_zero)

/-- The terminal interpreter is literally all-ideal at each actual available request under its executed post-call cap. -/
theorem lookup_terminal (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (entry : Coordinate (Fin n)) (table : Table (Fin n)) (calls : Nat)
    (bounded : DepthBound table calls) (available : Available table entry) (cap : calls + 1 ≤ positions) :
    PqxdhRecordLiftChainOracle.lookup source seeds (selected positions (positions * (n * 2))) entry =
      PqxdhRecordLiftChainOracle.lookup source seeds (fun _ => true) entry :=
  lookup_agrees source seeds _ _ entry ((selected_last entry).mpr
    (bounded_mono entry (available_bounded table calls bounded entry available) cap))

/-- At a noninitial selected step the predecessor has already been idealized. The direction-relative start excludes truncated-subtraction fallback coordinates. -/
theorem selected_predecessor (step : Fin (positions * (n * 2)))
    (later : start (entryAt step).direction < (entryAt step).position) :
    selected positions step.val (previous (entryAt step)) = true := by
  have bounded := at_bounded step
  have prior : Bounded positions (previous (entryAt step)) := by
    simp only [Bounded, previous] at bounded ⊢
    omega
  have advancePrior : advance (previous (entryAt step)) 1 = entryAt step := by
    have positive : 0 < (entryAt step).position := Nat.lt_of_le_of_lt (Nat.zero_le _) later
    have offset : (entryAt step).position - 1 + 1 = (entryAt step).position := Nat.sub_add_cancel positive
    simp only [previous, advance, offset]
  have laterBound : Bounded positions (advance (previous (entryAt step)) 1) := advancePrior.symm ▸ bounded
  have earlier := index_advance_lt (previous (entryAt step)) prior laterBound
  rw [selected_bounded _ prior]
  rw [decide_eq_true_eq]
  simpa only [advancePrior, index_at] using earlier

/-- A repeated coordinate retains its earlier complete answer in either mode, while still charging the actual source callback. This is the callback equation needed to reuse a challenge answer; no repeated native cost is dropped. -/
theorem lookup_repeated (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool) (entry : Coordinate (Fin n))
    (state : PqxdhRecordLiftChainCompiler.Execution (Fin n) PqxdhRecordLiftWorld.Primitive)
    (valid : PqxdhRecordLiftChainOracle.Valid source seeds ideal state.1)
    (value : PqxdhFullSecretInputKdf.FullOutput) (found : state.1 entry = some value) :
    (PqxdhRecordLiftChainOracle.lookup source seeds ideal entry).run state =
      pure (value, (state.1, PqxdhRecordLiftChainOracle.charge state.2)) := by
  cases mode : ideal entry with
  | true => exact PqxdhRecordLiftChainOracle.lookup_hit source seeds ideal entry state mode value found
  | false =>
    have stable : state.1.cacheQuery entry value = state.1 := by
      funext other
      by_cases same : other = entry
      · subst other; simp only [QueryCache.cacheQuery_self, found]
      · exact QueryCache.cacheQuery_of_ne state.1 value same
    rw [PqxdhRecordLiftChainOracle.lookup_real source seeds ideal entry state mode,
      PqxdhRecordLiftRealTable.record, ← valid.2 entry value mode found, stable]

end BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.coordinate_cellOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.coordinate_cellOf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.coordinate_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.coordinate_bounded

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.cellOf_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.cellOf_coordinate

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.at_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.at_index

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.at_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.at_bounded

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_at

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_injective

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_last

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_bounded

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_unchanged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_advance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_advance_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.index_advance_lt

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_adjacent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_adjacent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.bounded_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.bounded_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.available_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.available_bounded

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.depth_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.depth_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.depth_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.depth_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.depth_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.depth_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_terminal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_predecessor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.selected_predecessor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_repeated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder.lookup_repeated
