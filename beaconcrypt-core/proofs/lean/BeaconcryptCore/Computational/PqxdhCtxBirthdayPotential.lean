-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools
import BeaconcryptCore.Computational.CtxRomAuth

/-!
# The BLAKE2b birthday potential below the Server-authentication chain

The stopped birthday potential of the shared lazily sampled BLAKE2b-512 oracle `CtxRomAuth.ctxRandomOracle`, independent of any experiment, so that both the record-world term of CE-12 D-ct (`PqxdhDeploymentHeadlineDctHash.coll_world`) and the transcript-hash collision term of the Server-authentication game can use it without an import cycle.

- Moved unchanged from `PqxdhDeploymentHeadlineDctHash` (same qualified names, statements, bodies and exact guards): the collision event `CtxColl` (two distinct cached inputs with one digest; `ctxColl_collIn`: it is the generic `CollIn`), the stopped potential `drawPotential H n C` (`[CtxColl C] + ((H − n)·|C| + C(H − n, 2))/2^512` with `n ≤ H` counted reads, 0 beyond `H`), `draw_step` (one counted read of the oracle does not raise it in expectation) and `size_empty`.
- New. `drawPotential_shift`: a read reserved in the cap and spent from the count leave the potential unchanged. `drawPotential_mono_cap`: the potential is monotone in the cap. `expected_run_bounded_pair`: the budgeted supermartingale of `PqxdhDeploymentHeadlineDctTools.expected_run_bounded` with two costly query classes and separate `IsQueryBoundP` budgets. `cacheHasCollision_iff_ctxColl`: VCVio's `CacheHasCollision` on the BLAKE2b cache is `CtxColl` (the oracle's range is constant).

No assumption is used: every statement is about uniform sampling, VCVio's lazy random oracle and expected values.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash
open OracleComp.ProgramLogic (wp)
open PqxdhDeploymentHeadlineDctTools (size CollIn)

/-! ### The collision event and the counted potential (moved from `PqxdhDeploymentHeadlineDctHash`) -/

/-- Two distinct inputs of the BLAKE2b cache with one digest. -/
def CtxColl (cache : CtxRomAuth.CtxRO.QueryCache) : Prop := ∃ y z d, y ≠ z ∧ cache y = some d ∧ cache z = some d

/-- The collision event is the generic one at the BLAKE2b oracle. -/
theorem ctxColl_collIn (cache : CtxRomAuth.CtxRO.QueryCache) : CtxColl cache ↔ CollIn cache := Iff.rfl

open Classical in
/-- The stopped birthday potential with `H` counted calls allowed, after `n` counted calls on a cache. -/
noncomputable def drawPotential (H n : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) : ℝ≥0∞ :=
  if n ≤ H then
    (if CtxColl cache then 1 else 0) +
      (((H - n : ℕ) : ℝ≥0∞) * size cache + ((H - n).choose 2 : ℝ≥0∞)) * (2 ^ 512 : ℝ≥0∞)⁻¹
  else 0

/-- One counted read of the lazily sampled BLAKE2b oracle does not raise the stopped birthday potential in expectation: a miss hits one of `|C|` cached digests with chance `|C|/2^512`, and `(b-1)(m+1) + C(b-1,2) = b·m + C(b,2) - m`. -/
theorem draw_step (H n : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) (query : CtxRomAuth.CtxRO.Domain) :
    wp ((CtxRomAuth.ctxRandomOracle query).run cache) (fun r => drawPotential H (n + 1) r.2) ≤
      drawPotential H n cache := by
  classical
  by_cases room : n + 1 ≤ H
  · obtain ⟨b, hb⟩ : ∃ b, H - n = b + 1 := ⟨H - n - 1, by omega⟩
    have hb' : H - (n + 1) = b := by omega
    have expand : ∀ r : CtxRomAuth.CtxDigest × CtxRomAuth.CtxRO.QueryCache, drawPotential H (n + 1) r.2 =
        (if CtxColl r.2 then 1 else 0) + size r.2 * ((b : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹) +
          (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹ := by
      intro r
      simp only [drawPotential, room, ↓reduceIte, hb']
      ring
    simp only [expand]
    rw [OracleComp.ProgramLogic.wp_add, OracleComp.ProgramLogic.wp_add,
      OracleComp.ProgramLogic.wp_const_mul]
    have coll := PqxdhDeploymentHeadlineDctTools.ro_coll cache query
    have sized := PqxdhDeploymentHeadlineDctTools.ro_size cache query
    have constant : wp ((CtxRomAuth.ctxRandomOracle query).run cache)
        (fun _ => (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹) ≤ (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹ :=
      OracleComp.ProgramLogic.wp_le_const_of_support _ fun _ _ => le_rfl
    rw [CtxRomAuth.ctxDigest_card] at coll
    simp only [drawPotential, show n ≤ H by omega, ↓reduceIte, hb]
    calc _ ≤ ((if CtxColl cache then 1 else 0) + size cache * ((2 : ℝ≥0∞) ^ 512)⁻¹) +
          (size cache + 1) * ((b : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹) + (b.choose 2 : ℝ≥0∞) * (2 ^ 512 : ℝ≥0∞)⁻¹ := by
          gcongr
          · simp only [Nat.cast_pow, Nat.cast_ofNat] at coll
            exact coll
      _ = (if CtxColl cache then 1 else 0) +
          (((b + 1 : ℕ) : ℝ≥0∞) * size cache + ((b + 1).choose 2 : ℝ≥0∞)) * (2 ^ 512 : ℝ≥0∞)⁻¹ := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.cast_add, Nat.cast_add, Nat.cast_one]
          ring
  · have zero : ∀ r : CtxRomAuth.CtxDigest × CtxRomAuth.CtxRO.QueryCache, drawPotential H (n + 1) r.2 = 0 := by
      intro r
      simp only [drawPotential, room, ↓reduceIte]
    simp only [zero]
    exact le_trans (OracleComp.ProgramLogic.wp_le_const_of_support _ fun _ _ => le_rfl) zero_le

/-- The empty cache has no entry. -/
theorem size_empty : size (∅ : CtxRomAuth.CtxRO.QueryCache) = 0 := by
  unfold size
  simp

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash

namespace BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential
open OracleComp.ProgramLogic (wp)
open PqxdhDeploymentHeadlineDctTools (size)
open PqxdhDeploymentHeadlineDctHash (CtxColl drawPotential)

/-! ### Cap arithmetic of the stopped potential -/

/-- A read reserved in the cap and spent from the count leave the stopped potential unchanged. -/
theorem drawPotential_shift (H n : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) :
    drawPotential (H + 1) (n + 1) cache = drawPotential H n cache := by
  simp only [drawPotential, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- The stopped potential is monotone in the cap. -/
theorem drawPotential_mono_cap {H H' : ℕ} (le : H ≤ H') (n : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) :
    drawPotential H n cache ≤ drawPotential H' n cache := by
  unfold drawPotential
  by_cases inside : n ≤ H
  · have inside' : n ≤ H' := inside.trans le
    have gap : H - n ≤ H' - n := Nat.sub_le_sub_right le n
    simp only [inside, inside', ↓reduceIte]
    gcongr
  · simp only [inside, ↓reduceIte]
    exact zero_le

/-! ### The collision event -/

/-- VCVio's cache collision on the BLAKE2b cache is `CtxColl`: the oracle's range is constant, so the heterogeneous equality is an equality. -/
theorem cacheHasCollision_iff_ctxColl (cache : CtxRomAuth.CtxRO.QueryCache) :
    CacheHasCollision cache ↔ CtxColl cache := by
  constructor
  · rintro ⟨y, z, u, v, ne, found, other, same⟩
    have equal : u = v := eq_of_heq same
    subst equal
    exact ⟨y, z, u, ne, found, other⟩
  · rintro ⟨y, z, d, ne, found, other⟩
    exact ⟨y, z, d, d, ne, found, other, HEq.rfl⟩

/-! ### A budgeted supermartingale with two costly classes -/

section Budget
variable {ι' : Type} {spec : OracleSpec ι'} {σ α : Type}

/-- A potential indexed by two remaining budgets: a query of the first class may spend one unit of the first budget, a query of the second class (and not the first) one unit of the second, any other query none. Then over a whole simulation whose queries of each class are bounded separately (`IsQueryBoundP`), the expected final potential at budgets 0 is at most the initial potential at the two budgets of the program. -/
theorem expected_run_bounded_pair (impl : QueryImpl spec (StateT σ ProbComp)) (first second : ι' → Prop)
    [DecidablePred first] [DecidablePred second] (potential : ℕ → ℕ → σ → ℝ≥0∞)
    (monoFirst : ∀ a b state, potential a b state ≤ potential (a + 1) b state)
    (monoSecond : ∀ a b state, potential a b state ≤ potential a (b + 1) state)
    (paidFirst : ∀ query state a b, first query →
      wp ((impl query).run state) (fun result => potential a b result.2) ≤ potential (a + 1) b state)
    (paidSecond : ∀ query state a b, ¬ first query → second query →
      wp ((impl query).run state) (fun result => potential a b result.2) ≤ potential a (b + 1) state)
    (free : ∀ query state a b, ¬ first query → ¬ second query →
      wp ((impl query).run state) (fun result => potential a b result.2) ≤ potential a b state)
    (work : OracleComp spec α) (a b : ℕ) (boundedFirst : work.IsQueryBoundP first a)
    (boundedSecond : work.IsQueryBoundP second b) (state : σ) :
    wp ((simulateQ impl work).run state) (fun result => potential 0 0 result.2) ≤ potential a b state := by
  induction work using OracleComp.inductionOn generalizing state a b with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, OracleComp.ProgramLogic.wp_pure]
      clear boundedFirst boundedSecond
      have second : ∀ b, potential 0 0 state ≤ potential 0 b state := by
        intro b
        induction b with
        | zero => exact le_rfl
        | succ n ih => exact ih.trans (monoSecond 0 n state)
      induction a with
      | zero => exact second b
      | succ n ih => exact ih.trans (monoFirst n b state)
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at boundedFirst boundedSecond
      rw [simulateQ_query_bind, StateT.run_bind, OracleComp.ProgramLogic.wp_bind]
      by_cases hf : first query
      · have positive : 0 < a := boundedFirst.1.resolve_left (not_not.mpr hf)
        obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
        refine le_trans (OracleComp.ProgramLogic.wp_mono ((impl query).run state) ?_) (paidFirst query state n b hf)
        intro result
        have restFirst := boundedFirst.2 result.1
        simp only [hf, ite_true, Nat.add_sub_cancel] at restFirst
        have restSecond := boundedSecond.2 result.1
        by_cases hs : second query
        · have positive' : 0 < b := boundedSecond.1.resolve_left (not_not.mpr hs)
          obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
          simp only [hs, ite_true, Nat.add_sub_cancel] at restSecond
          exact (ih result.1 n m restFirst restSecond result.2).trans (monoSecond n m result.2)
        · simp only [hs, ite_false] at restSecond
          exact ih result.1 n b restFirst restSecond result.2
      · have restFirst := boundedFirst.2
        simp only [hf, ite_false] at restFirst
        by_cases hs : second query
        · have positive : 0 < b := boundedSecond.1.resolve_left (not_not.mpr hs)
          obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
          refine le_trans (OracleComp.ProgramLogic.wp_mono ((impl query).run state) ?_)
            (paidSecond query state a m hf hs)
          intro result
          have restSecond := boundedSecond.2 result.1
          simp only [hs, ite_true, Nat.add_sub_cancel] at restSecond
          exact ih result.1 a m (restFirst result.1) restSecond result.2
        · refine le_trans (OracleComp.ProgramLogic.wp_mono ((impl query).run state) ?_) (free query state a b hf hs)
          intro result
          have restSecond := boundedSecond.2 result.1
          simp only [hs, ite_false] at restSecond
          exact ih result.1 a b (restFirst result.1) restSecond result.2

end Budget

end BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential

-- Axiom guards (moved byte-identically from `PqxdhDeploymentHeadlineDctHash`)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.ctxColl_collIn' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.ctxColl_collIn

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.draw_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.draw_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.size_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash.size_empty

-- Axiom guards of the new declarations (generated from kernel output)

/--
info: 'BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.drawPotential_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.drawPotential_shift

/--
info: 'BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.drawPotential_mono_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.drawPotential_mono_cap

/--
info: 'BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.cacheHasCollision_iff_ctxColl' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.cacheHasCollision_iff_ctxColl

/--
info: 'BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.expected_run_bounded_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential.expected_run_bounded_pair
