-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-!
# Couplings of probabilistic computations with relabelled coins and escapes (items 4 and 5, world facts)

`Swap R x y` is a syntactic coupling of two probabilistic computations `x` and `y` (uniform-coin programs, `ProbComp`): either both return values related by `R`; or both draw the same coin, the coin of `y` relabelled by a bijection `σ` of the coin's range (`query_bind`), and the continuations are coupled at every coin `r` and `σ r`; or both run unrelated first parts `x'` and `y'` whose reachable outputs are related by `P` pairwise (an escape, `product`), followed by continuations coupled on `P`-related outputs. A bijection preserves the uniform law of a coin, and an escape relates every output of one side with every output of the other, so a coupling identifies the laws of any two Boolean observations that agree on related values (`Swap.evalDist_map`).

`Swap.simulateQ_run` transports couplings through the simulation of one program under two stateful implementations: if every single query, from related states, is coupled so that the replies are equal and the states related, or so that both states satisfy escape predicates `B₁` and `B₂` that every later query keeps, then the whole simulation is coupled in the same way. `Swap.refl` couples a computation with itself; `Swap.bind`, `Swap.map` and `Swap.escape` compose couplings.

No contract and no assumption. New Claude work.
-/

open OracleComp OracleSpec MeasureTheory
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftSwap

/-- Two probabilistic computations are coupled: related final values; the same coin drawn on both sides with the right coin relabelled by a bijection; or unrelated first parts whose reachable outputs are pairwise related, followed by coupled continuations. -/
inductive Swap : {α β : Type} → (α → β → Prop) → ProbComp α → ProbComp β → Prop
  | pure {α β : Type} {R : α → β → Prop} (a : α) (b : β) : R a b → Swap R (pure a) (pure b)
  | query_bind {α β : Type} {R : α → β → Prop} (n : ℕ) (σ : unifSpec.Range n → unifSpec.Range n)
      (bijective : Function.Bijective σ) (k₁ : unifSpec.Range n → ProbComp α) (k₂ : unifSpec.Range n → ProbComp β) :
      (∀ r, Swap R (k₁ r) (k₂ (σ r))) →
      Swap R ((unifSpec.query n : ProbComp _) >>= k₁) ((unifSpec.query n : ProbComp _) >>= k₂)
  | product {α β γ δ : Type} {R : α → β → Prop} (x : ProbComp γ) (y : ProbComp δ) (P : γ → δ → Prop)
      (related : ∀ a ∈ support x, ∀ b ∈ support y, P a b) (f : γ → ProbComp α) (g : δ → ProbComp β) :
      (∀ a b, P a b → Swap R (f a) (g b)) → Swap R (x >>= f) (y >>= g)

/-- Couplings weaken to any larger relation on final values. -/
theorem Swap.mono {α β : Type} {R R' : α → β → Prop} {x : ProbComp α} {y : ProbComp β} (h : Swap R x y)
    (weaker : ∀ a b, R a b → R' a b) : Swap R' x y := by
  induction h with
  | pure a b hab => exact .pure a b (weaker a b hab)
  | query_bind n σ bijective k₁ k₂ _ ih => exact .query_bind n σ bijective k₁ k₂ fun r => ih r weaker
  | product x y P related f g _ ih => exact .product x y P related f g fun a b hab => ih a b hab weaker

/-- Couplings compose with continuations that are coupled on related values. -/
theorem Swap.bind {α β γ δ : Type} {R : α → β → Prop} {R' : γ → δ → Prop} {x : ProbComp α} {y : ProbComp β}
    (h : Swap R x y) {f : α → ProbComp γ} {g : β → ProbComp δ} (next : ∀ a b, R a b → Swap R' (f a) (g b)) :
    Swap R' (x >>= f) (y >>= g) := by
  induction h with
  | pure a b hab => simpa only [pure_bind] using next a b hab
  | query_bind n σ bijective k₁ k₂ _ ih =>
      simp only [bind_assoc]
      exact .query_bind n σ bijective _ _ fun r => ih r next
  | product x y P related f₀ g₀ _ ih =>
      simp only [bind_assoc]
      exact .product x y P related _ _ fun a b hab => ih a b hab next

/-- Couplings survive maps that send related values to related values. -/
theorem Swap.map {α β γ δ : Type} {R : α → β → Prop} {R' : γ → δ → Prop} {x : ProbComp α} {y : ProbComp β}
    (h : Swap R x y) {f : α → γ} {g : β → δ} (related : ∀ a b, R a b → R' (f a) (g b)) :
    Swap R' (f <$> x) (g <$> y) := by
  simp only [map_eq_bind_pure_comp]
  exact h.bind fun a b hab => .pure _ _ (related a b hab)

/-- A computation is coupled with itself (every coin drawn equally) for any reflexive relation. -/
theorem Swap.refl {α : Type} (x : ProbComp α) {R : α → α → Prop} (diag : ∀ a, R a a) : Swap R x x := by
  induction x using OracleComp.inductionOn with
  | pure a => exact .pure a a (diag a)
  | query_bind n k ih => exact .query_bind n id Function.bijective_id k k fun r => ih r

/-- A computation is coupled with itself (every coin drawn equally) for any relation that is reflexive on its reachable outputs. -/
theorem Swap.refl_support {α : Type} (x : ProbComp α) {R : α → α → Prop} (diag : ∀ a ∈ support x, R a a) :
    Swap R x x := by
  induction x using OracleComp.inductionOn with
  | pure a => exact .pure a a (diag a (by simp))
  | query_bind n k ih =>
      exact .query_bind n id Function.bijective_id k k fun r =>
        ih r fun a ha => diag a ((MonadAttach.mem_support_bind).mpr ⟨r, by simp, ha⟩)

/-- Two computations whose reachable outputs are pairwise related are coupled. -/
theorem Swap.escape {α β : Type} {R : α → β → Prop} (x : ProbComp α) (y : ProbComp β)
    (related : ∀ a ∈ support x, ∀ b ∈ support y, R a b) : Swap R x y := by
  have h := Swap.product (R := R) x y R related (fun a => (Pure.pure a : ProbComp α))
    (fun b => (Pure.pure b : ProbComp β)) fun a b hab => .pure a b hab
  simpa only [bind_pure] using h

/-- A single coin, relabelled on the right by a bijection, is coupled with itself. -/
theorem Swap.query (n : ℕ) (σ : unifSpec.Range n → unifSpec.Range n) (bijective : Function.Bijective σ) :
    Swap (fun r₁ r₂ => r₂ = σ r₁) (unifSpec.query n : ProbComp _) (unifSpec.query n : ProbComp _) := by
  have h := Swap.query_bind (R := fun r₁ r₂ => r₂ = σ r₁) n σ bijective
    (fun r => (Pure.pure r : ProbComp (unifSpec.Range n))) (fun r => (Pure.pure r : ProbComp (unifSpec.Range n)))
    fun r => .pure r (σ r) rfl
  simpa only [bind_pure] using h

/-- **Law equality.** Coupled computations give the same law to any two Boolean observations that agree on related values. -/
theorem Swap.evalDist_map {α β : Type} {R : α → β → Prop} {x : ProbComp α} {y : ProbComp β} (h : Swap R x y)
    (F : α → Bool) (G : β → Bool) (agree : ∀ a b, R a b → F a = G b) : 𝒟[F <$> x] = 𝒟[G <$> y] := by
  induction h with
  | pure a b hab => simp only [map_pure, agree a b hab]
  | query_bind n σ bijective k₁ k₂ _ ih =>
      simp only [map_bind]
      calc 𝒟[(unifSpec.query n : ProbComp _) >>= fun r => F <$> k₁ r]
          = 𝒟[(unifSpec.query n : ProbComp _) >>= fun r => G <$> k₂ (σ r)] :=
            evalDist_bind_congr _ _ _ fun r => ih r agree
        _ = 𝒟[(unifSpec.query n : ProbComp _) >>= fun r => G <$> k₂ r] :=
            evalDist_bind_bijective_of_uniform _ (evalDist_query_uniform n) σ bijective fun r => G <$> k₂ r
  | product x y P related f g _ ih =>
      obtain ⟨a₀, ha₀⟩ := OracleComp.support_nonempty x
      obtain ⟨b₀, hb₀⟩ := OracleComp.support_nonempty y
      have center : 𝒟[F <$> f a₀] = 𝒟[G <$> g b₀] := ih a₀ b₀ (related a₀ ha₀ b₀ hb₀) agree
      simp only [map_bind]
      calc 𝒟[x >>= fun a => F <$> f a] = 𝒟[x >>= fun _ => G <$> g b₀] :=
            OracleComp.evalDist_bind_congr_of_support _ _ _ fun a ha => ih a b₀ (related a ha b₀ hb₀) agree
        _ = 𝒟[G <$> g b₀] := OracleComp.evalDist_bind_const _ _
        _ = 𝒟[F <$> f a₀] := center.symm
        _ = 𝒟[y >>= fun _ => F <$> f a₀] := (OracleComp.evalDist_bind_const _ _).symm
        _ = 𝒟[y >>= fun b => G <$> g b] :=
            OracleComp.evalDist_bind_congr_of_support _ _ _ fun b hb => ih a₀ b (related a₀ ha₀ b hb) agree


/-! ### Simulation -/

section Simulation
variable {ι : Type} {spec : OracleSpec ι}

/-- A state predicate that every query keeps is kept by every simulated program. -/
theorem support_keep {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (B : σ → Prop)
    (keep : ∀ q s, B s → ∀ p ∈ support ((impl q).run s), B p.2) {α : Type} (oa : OracleComp spec α) (s : σ)
    (hs : B s) : ∀ p ∈ support ((simulateQ impl oa).run s), B p.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      intro p hp
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hs
  | query_bind q k ih =>
      intro p hp
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind] at hp
      obtain ⟨mid, hmid, hp⟩ := (MonadAttach.mem_support_bind).mp hp
      exact ih mid.1 mid.2 (keep q s hs mid hmid) p hp

/-- The relation of a coupled simulation: equal values and related states, or both states escaped. -/
def SimRel {α σ₁ σ₂ : Type} (S : σ₁ → σ₂ → Prop) (B₁ : σ₁ → Prop) (B₂ : σ₂ → Prop) (p₁ : α × σ₁)
    (p₂ : α × σ₂) : Prop :=
  (p₁.1 = p₂.1 ∧ S p₁.2 p₂.2) ∨ (B₁ p₁.2 ∧ B₂ p₂.2)

/-- **Transport.** One program simulated under two stateful implementations, from related states: if every single query from related states is coupled with equal replies and related states or with both states escaped, and the escape predicates are kept by every query, the simulations are coupled in the same way. -/
theorem Swap.simulateQ_run {σ₁ σ₂ : Type} (first : QueryImpl spec (StateT σ₁ ProbComp))
    (second : QueryImpl spec (StateT σ₂ ProbComp)) (S : σ₁ → σ₂ → Prop) (B₁ : σ₁ → Prop) (B₂ : σ₂ → Prop)
    (keep₁ : ∀ q s, B₁ s → ∀ p ∈ support ((first q).run s), B₁ p.2)
    (keep₂ : ∀ q s, B₂ s → ∀ p ∈ support ((second q).run s), B₂ p.2)
    (step : ∀ q s t, S s t → Swap (SimRel S B₁ B₂) ((first q).run s) ((second q).run t)) {α : Type}
    (oa : OracleComp spec α) (s : σ₁) (t : σ₂) (related : S s t) :
    Swap (SimRel S B₁ B₂) ((simulateQ first oa).run s) ((simulateQ second oa).run t) := by
  induction oa using OracleComp.inductionOn generalizing s t with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact .pure _ _ (Or.inl ⟨rfl, related⟩)
  | query_bind q k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      refine (step q s t related).bind fun p₁ p₂ hp => ?_
      rcases hp with ⟨same, hS⟩ | ⟨h₁, h₂⟩
      · rw [← same]
        exact ih p₁.1 p₁.2 p₂.2 hS
      · exact Swap.escape _ _ fun a ha b hb =>
          Or.inr ⟨support_keep first B₁ keep₁ _ _ h₁ a ha, support_keep second B₂ keep₂ _ _ h₂ b hb⟩

end Simulation

end BeaconcryptCore.Computational.PqxdhRecordLiftSwap

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.refl_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.refl_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.escape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.escape

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.evalDist_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.evalDist_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.support_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.support_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.simulateQ_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSwap.Swap.simulateQ_run
