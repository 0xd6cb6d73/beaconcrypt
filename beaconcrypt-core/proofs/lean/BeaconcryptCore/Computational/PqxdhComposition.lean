import BeaconcryptCore.Computational.PqxdhJointKdfGame

/-!
# Explicit finite global-hybrid accounting

The games below are whole experiments, including all sessions, correlated keys, compromise decisions, and observations. The arithmetic does not replace this context by independent one-key experiments. Applying a component bound requires a separate reduction for each adjacent pair in that SAME global context. No such ratchet/session reduction is assumed or proved here.
-/

open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhComposition

/-- Replacing `n` global hybrid steps charges the sum of all adjacent distinguishing gaps. -/
theorem finiteHybridBound (game : ℕ → ProbComp Bool) (n : ℕ) :
    (game 0).boolDistAdvantage (game n) ≤
      ∑ i ∈ Finset.range n, (game i).boolDistAdvantage (game (i + 1)) := by
  induction n with
  | zero => simp [ProbComp.boolDistAdvantage]
  | succ n ih =>
      calc
        _ ≤ (game 0).boolDistAdvantage (game n) +
            (game n).boolDistAdvantage (game (n + 1)) :=
          ProbComp.boolDistAdvantage_triangle _ _ _
        _ ≤ (∑ i ∈ Finset.range n, (game i).boolDistAdvantage (game (i + 1))) +
            (game n).boolDistAdvantage (game (n + 1)) := add_le_add ih (le_refl _)
        _ = _ := (Finset.sum_range_succ _ n).symm

/-- Component losses can be added only after every adjacent global-game reduction has been supplied. -/
theorem finiteHybridBound_of_hop_bounds (game : ℕ → ProbComp Bool) (n : ℕ)
    (loss : ℕ → ℝ)
    (hop : ∀ i < n, (game i).boolDistAdvantage (game (i + 1)) ≤ loss i) :
    (game 0).boolDistAdvantage (game n) ≤ ∑ i ∈ Finset.range n, loss i := by
  exact (finiteHybridBound game n).trans
    (Finset.sum_le_sum (fun i hi => hop i (Finset.mem_range.mp hi)))

/-- A common per-hop loss incurs an explicit `n`-fold charge, not a free multi-key lifting. -/
theorem finiteHybridBound_uniform_loss (game : ℕ → ProbComp Bool) (n : ℕ) (loss : ℝ)
    (hop : ∀ i < n, (game i).boolDistAdvantage (game (i + 1)) ≤ loss) :
    (game 0).boolDistAdvantage (game n) ≤ n * loss := by
  simpa using finiteHybridBound_of_hop_bounds game n (fun _ => loss) hop

end BeaconcryptCore.Computational.PqxdhComposition

/--
info: 'BeaconcryptCore.Computational.PqxdhComposition.finiteHybridBound_uniform_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhComposition.finiteHybridBound_uniform_loss
