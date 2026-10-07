-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# Erasing discarded lazy-oracle queries

This generic component has no protocol content. Two probabilistic programs have the same law (`LawEq`) when every continuation into any measurable space sees the same `𝒟` measure. A lens focuses a lazily sampled cache inside a larger state. Completing one point of that cache is the lazy query at the point with its answer dropped. A step `Commutes` with the lens when completing any point before the step has the same law as completing it after the step.

`discard_erase` is the global erasure: if every query of a handler is, in law, a pointed step followed by the completion of the point it reports, and every pointed step commutes with completions, then the handler and the pointed handler without completions have the same law under any continuation that is blind to completions. This is an equality in law of lazy sampling, not a statement about any concrete function. Its hypotheses `factor`, `oblivious` and `blind` (the continuation is `Blind`) are obligations on the given handler, pointed handler and continuation, proved for each instance; no probabilistic independence or noninterference assumption is taken.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.LazyOracleDiscard

/-- Contextual law equality: every continuation into any measurable space sees the same measure. -/
def LawEq {α : Type} (mx my : ProbComp α) : Prop :=
  ∀ (β : Type) [MeasurableSpace β] (k : α → ProbComp β), 𝒟[mx >>= k] = 𝒟[my >>= k]

/-- Law equality is reflexive. -/
theorem LawEq.refl {α : Type} (mx : ProbComp α) : LawEq mx mx :=
  fun _ _ _ => rfl

/-- Law equality is symmetric. -/
theorem LawEq.symm {α : Type} {mx my : ProbComp α} (h : LawEq mx my) : LawEq my mx :=
  fun β _ k => (h β k).symm

/-- Law equality is transitive. -/
theorem LawEq.trans {α : Type} {mx my mz : ProbComp α} (h₁ : LawEq mx my) (h₂ : LawEq my mz) :
    LawEq mx mz :=
  fun β _ k => (h₁ β k).trans (h₂ β k)

/-- Equal programs have the same law. -/
theorem LawEq.of_eq {α : Type} {mx my : ProbComp α} (h : mx = my) : LawEq mx my := by
  subst h
  exact LawEq.refl mx

/-- Law equality is a congruence for `bind`. -/
theorem LawEq.bind {α β : Type} {mx my : ProbComp α} {f g : α → ProbComp β}
    (h : LawEq mx my) (hk : ∀ a, LawEq (f a) (g a)) : LawEq (mx >>= f) (my >>= g) := by
  intro γ _ k
  simp only [bind_assoc]
  rw [evalDist_bind_congr mx (fun a => f a >>= k) (fun a => g a >>= k) (fun a => hk a γ k)]
  exact h γ (fun a => g a >>= k)

/-- Law equality is a congruence for `map`. -/
theorem LawEq.map {α β : Type} {mx my : ProbComp α} (f : α → β) (h : LawEq mx my) :
    LawEq (f <$> mx) (f <$> my) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact h.bind fun _ => LawEq.refl _

/-- With a measurable space on the result, law equality gives equal measures. -/
theorem LawEq.evalDist_eq {α : Type} [MeasurableSpace α] {mx my : ProbComp α} (h : LawEq mx my) :
    𝒟[mx] = 𝒟[my] := by
  simpa only [bind_pure] using h α (pure : α → ProbComp α)

/-- Two independent draws may be taken in either order. The proof is an induction over both programs: every uniform draw of a probabilistic program has a finite index type, so VCVio's measure-level swap for countable draws applies one draw at a time. -/
theorem lawEq_swap {α β γ : Type} (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp γ) :
    LawEq (mx >>= fun a => my >>= fun b => f a b) (my >>= fun b => mx >>= fun a => f a b) := by
  intro δ _ k
  simp only [bind_assoc]
  have draw_swap : ∀ (n : ℕ) (my : ProbComp β) (g : Fin (n + 1) → β → ProbComp δ),
      𝒟[$[0..n] >>= fun r => my >>= g r] = 𝒟[my >>= fun b => $[0..n] >>= fun r => g r b] := by
    intro n my
    induction my using ProbComp.inductionOn with
    | pure b => intro g; simp only [pure_bind]
    | query_bind n' c ih =>
      intro g
      simp only [bind_assoc]
      refine (evalDist_bind_bind_swap_of_countable ($[0..n]) ($[0..n'])
        (fun r r' => c r' >>= g r)).trans ?_
      exact evalDist_bind_congr _ _ _ fun r' => ih r' g
  induction mx using ProbComp.inductionOn with
  | pure a => simp only [pure_bind]
  | query_bind n c ih =>
    simp only [bind_assoc]
    refine (evalDist_bind_congr _ _ _ fun r => ih r).trans ?_
    exact draw_swap n my (fun r b => c r >>= fun a => f a b >>= k)

/-- An unused draw can be dropped, because a probabilistic program never fails. -/
theorem lawEq_drop {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    LawEq (mx >>= fun _ => my) my := by
  intro γ _ k
  rw [bind_assoc]
  exact OracleComp.evalDist_bind_const mx (my >>= k)

/-- A get/set lens with the three very-well-behaved laws. -/
structure StateLens (σ ρ : Type) where
  get : σ → ρ
  set : σ → ρ → σ
  get_set : ∀ s r, get (set s r) = r
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s r r', set (set s r) r' = set s r'

namespace StateLens

/-- The whole state. -/
def id (σ : Type) : StateLens σ σ :=
  ⟨fun s => s, fun _ r => r, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The first component of a pair. -/
def fst (σ ρ : Type) : StateLens (σ × ρ) σ :=
  ⟨Prod.fst, fun s r => (r, s.2), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The second component of a pair. -/
def snd (σ ρ : Type) : StateLens (σ × ρ) ρ :=
  ⟨Prod.snd, fun s r => (s.1, r), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- Focus through an outer lens, then an inner one. -/
def comp {σ ρ π : Type} (outer : StateLens σ ρ) (inner : StateLens ρ π) : StateLens σ π where
  get s := inner.get (outer.get s)
  set s p := outer.set s (inner.set (outer.get s) p)
  get_set s p := by simp only [outer.get_set, inner.get_set]
  set_get s := by simp only [inner.set_get, outer.set_get]
  set_set s p p' := by simp only [outer.get_set, inner.set_set, outer.set_set]

/-- Run an inner stateful step on the focused coordinate. -/
def lift {σ ρ α : Type} (E : StateLens σ ρ) (step : StateT ρ ProbComp α) : StateT σ ProbComp α :=
  fun s => (fun r => (r.1, E.set s r.2)) <$> step.run (E.get s)

end StateLens

section Cache
variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- A lens onto a lazily sampled cache. -/
abbrev CacheLens (spec : OracleSpec ι) (σ : Type) := StateLens σ spec.QueryCache

/-- Complete one point of a lazy cache: the lazy query at that point with its answer dropped. -/
noncomputable def complete (t : spec.Domain) (cache : spec.QueryCache) : ProbComp spec.QueryCache :=
  Prod.snd <$> (spec.randomOracle t).run cache

/-- A present point is kept; an absent point receives one fresh uniform answer. -/
theorem complete_run (t : spec.Domain) (cache : spec.QueryCache) :
    complete t cache = match cache t with
      | some _ => pure cache
      | none => (fun u => cache.cacheQuery t u) <$> ($ᵗ spec.Range t) := by
  unfold complete
  rw [randomOracle.run_eq]
  rcases cache t with _ | u
  · simp
  · simp

namespace StateLens
variable {σ : Type}

/-- Complete one point of the focused cache. -/
noncomputable def complete (L : CacheLens spec σ) (t : spec.Domain) (s : σ) : ProbComp σ :=
  L.set s <$> LazyOracleDiscard.complete t (L.get s)

/-- Complete an optional point; `none` changes nothing. -/
noncomputable def completeOpt (L : CacheLens spec σ) : Option spec.Domain → σ → ProbComp σ
  | none, s => pure s
  | some t, s => L.complete t s

/-- The lazy query on the focused cache. -/
noncomputable def query (L : CacheLens spec σ) (t : spec.Domain) : StateT σ ProbComp (spec.Range t) :=
  fun s => (fun r => (r.1, L.set s r.2)) <$> (spec.randomOracle t).run (L.get s)

end StateLens

/-- One step commutes, in law, with completing any point of the lensed cache. -/
def Commutes {σ : Type} (L : CacheLens spec σ) {α : Type} (step : StateT σ ProbComp α) : Prop :=
  ∀ (t : spec.Domain) (s : σ),
    LawEq (L.complete t s >>= step.run) (step.run s >>= fun r => (r.1, ·) <$> L.complete t r.2)

/-- A continuation that cannot observe completions of the lensed cache. -/
def Blind {σ : Type} (L : CacheLens spec σ) {α γ : Type} (k : α × σ → ProbComp γ) : Prop :=
  ∀ (a : α) (t : spec.Domain) (s : σ), LawEq (L.complete t s >>= fun s' => k (a, s')) (k (a, s))

/-- Completing an absent point draws one uniform answer. -/
theorem complete_of_none {t : spec.Domain} {cache : spec.QueryCache} (h : cache t = none) :
    complete t cache = (fun u => cache.cacheQuery t u) <$> ($ᵗ spec.Range t) := by
  rw [complete_run, h]

/-- Completing a present point changes nothing. -/
theorem complete_of_some {t : spec.Domain} {cache : spec.QueryCache} {v : spec.Range t}
    (h : cache t = some v) : complete t cache = pure cache := by
  rw [complete_run, h]

/-- A lazy query at an absent point draws and records one uniform answer. -/
theorem query_of_none {u : spec.Domain} {cache : spec.QueryCache} (h : cache u = none) :
    (spec.randomOracle u).run cache =
      ($ᵗ spec.Range u) >>= fun y => pure (y, cache.cacheQuery u y) := by
  rw [randomOracle.run_eq, h]

/-- A lazy query at a present point returns the recorded answer. -/
theorem query_of_some {u : spec.Domain} {cache : spec.QueryCache} {w : spec.Range u}
    (h : cache u = some w) : (spec.randomOracle u).run cache = pure (w, cache) := by
  rw [randomOracle.run_eq, h]

/-- The cache-level core: completing a point and one lazy query commute in law. -/
theorem complete_query_swap (t u : spec.Domain) (c : spec.QueryCache) :
    LawEq (complete t c >>= (spec.randomOracle u).run)
      ((spec.randomOracle u).run c >>= fun r => (r.1, ·) <$> complete t r.2) := by
  rcases ht : c t with _ | v
  · by_cases htu : u = t
    · subst htu
      apply LawEq.of_eq
      rw [complete_of_none ht, query_of_none ht, bind_map_left, bind_assoc]
      refine bind_congr fun x => ?_
      rw [query_of_some (QueryCache.cacheQuery_self c u x), pure_bind,
        complete_of_some (QueryCache.cacheQuery_self c u x), map_pure]
    · rcases hu : c u with _ | w
      · have hcomm : ∀ x y, (c.cacheQuery t x).cacheQuery u y = (c.cacheQuery u y).cacheQuery t x :=
          fun x y => Function.update_comm (Ne.symm htu) _ _ c
        have lhs : complete t c >>= (spec.randomOracle u).run =
            ($ᵗ spec.Range t) >>= fun x => ($ᵗ spec.Range u) >>= fun y =>
              pure (y, (c.cacheQuery u y).cacheQuery t x) := by
          rw [complete_of_none ht, bind_map_left]
          refine bind_congr fun x => ?_
          rw [query_of_none ((QueryCache.cacheQuery_of_ne c x htu).trans hu)]
          simp only [hcomm]
        have rhs : ((spec.randomOracle u).run c >>= fun r => (r.1, ·) <$> complete t r.2) =
            ($ᵗ spec.Range u) >>= fun y => ($ᵗ spec.Range t) >>= fun x =>
              pure (y, (c.cacheQuery u y).cacheQuery t x) := by
          rw [query_of_none hu, bind_assoc]
          refine bind_congr fun y => ?_
          rw [pure_bind, complete_of_none ((QueryCache.cacheQuery_of_ne c y (Ne.symm htu)).trans ht),
            Functor.map_map, map_eq_bind_pure_comp]
          rfl
        rw [lhs, rhs]
        exact lawEq_swap _ _ _
      · apply LawEq.of_eq
        rw [complete_of_none ht, query_of_some hu, pure_bind, complete_of_none ht, bind_map_left,
          Functor.map_map, map_eq_bind_pure_comp]
        refine bind_congr fun x => ?_
        rw [query_of_some ((QueryCache.cacheQuery_of_ne c x htu).trans hu)]
        rfl
  · apply LawEq.of_eq
    rw [complete_of_some ht, pure_bind]
    rcases hu : c u with _ | w
    · have htu : t ≠ u := by
        intro h
        subst h
        rw [ht] at hu
        cases hu
      rw [query_of_none hu, bind_assoc]
      refine bind_congr fun y => ?_
      rw [pure_bind, complete_of_some ((QueryCache.cacheQuery_of_ne c y htu).trans ht), map_pure]
    · rw [query_of_some hu, pure_bind, complete_of_some ht, map_pure]

/-- The pure step commutes with every completion. -/
theorem commutes_pure {σ α : Type} (L : CacheLens spec σ) (a : α) :
    Commutes L (pure a : StateT σ ProbComp α) := by
  intro t s
  apply LawEq.of_eq
  show L.complete t s >>= (fun s' => (pure a : StateT σ ProbComp α).run s') =
    (pure a : StateT σ ProbComp α).run s >>= fun r => (r.1, ·) <$> L.complete t r.2
  simp only [StateT.run_pure, pure_bind]
  rw [map_eq_bind_pure_comp]
  rfl

/-- Commutation is closed under `bind`. -/
theorem commutes_bind {σ α β : Type} (L : CacheLens spec σ) {x : StateT σ ProbComp α}
    {f : α → StateT σ ProbComp β} (hx : Commutes L x) (hf : ∀ a, Commutes L (f a)) :
    Commutes L (x >>= f) := by
  intro t s
  have first := LawEq.bind (hx t s) (fun r => LawEq.refl ((f r.1).run r.2))
  have second : LawEq (x.run s >>= fun r => L.complete t r.2 >>= (f r.1).run)
      (x.run s >>= fun r => (f r.1).run r.2 >>= fun r' => (r'.1, ·) <$> L.complete t r'.2) :=
    LawEq.bind (LawEq.refl _) (fun r => hf r.1 t r.2)
  have hrun : (x >>= f).run = fun s' => x.run s' >>= fun p => (f p.1).run p.2 :=
    funext fun s' => StateT.run_bind x f s'
  simp only [hrun]
  rw [← bind_assoc]
  refine first.trans ?_
  simpa only [bind_assoc, bind_map_left] using second

/-- Commutation is closed under `map`. -/
theorem commutes_map {σ α β : Type} (L : CacheLens spec σ) {x : StateT σ ProbComp α} (f : α → β)
    (hx : Commutes L x) : Commutes L (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact commutes_bind L hx (fun a => commutes_pure L (f a))

/-- A step that never reads or writes the focused cache commutes with every completion. -/
theorem commutes_frame {σ α : Type} (L : CacheLens spec σ) (step : StateT σ ProbComp α)
    (indep : ∀ s c, step.run (L.set s c) = (fun r => (r.1, L.set r.2 c)) <$> step.run s) :
    Commutes L step := by
  intro t s
  have keep : step.run s = (fun r => (r.1, L.set r.2 (L.get s))) <$> step.run s := by
    simpa only [L.set_get] using indep s (L.get s)
  have lhs : L.complete t s >>= step.run =
      complete t (L.get s) >>= fun c => step.run s >>= fun r => pure (r.1, L.set r.2 c) := by
    rw [StateLens.complete, bind_map_left]
    refine bind_congr fun c => ?_
    rw [indep, map_eq_bind_pure_comp]
    rfl
  have rhs : (step.run s >>= fun r => (r.1, ·) <$> L.complete t r.2) =
      step.run s >>= fun r => complete t (L.get s) >>= fun c => pure (r.1, L.set r.2 c) := by
    conv_lhs => rw [keep]
    rw [bind_map_left]
    refine bind_congr fun r => ?_
    rw [StateLens.complete, L.get_set, Functor.map_map, map_eq_bind_pure_comp]
    simp only [L.set_set]
    rfl
  rw [lhs, rhs]
  exact lawEq_swap _ _ _

/-- The lazy query on the focused cache commutes with completing any point. -/
theorem commutes_query {σ : Type} (L : CacheLens spec σ) (u : spec.Domain) : Commutes L (L.query u) := by
  intro t s
  have lhs : L.complete t s >>= (L.query u).run =
      (fun r => (r.1, L.set s r.2)) <$> (complete t (L.get s) >>= (spec.randomOracle u).run) := by
    simp only [StateLens.complete, StateLens.query, StateT.run, bind_map_left, map_bind,
      L.get_set, L.set_set]
  have rhs : ((L.query u).run s >>= fun r => (r.1, ·) <$> L.complete t r.2) =
      (fun r => (r.1, L.set s r.2)) <$>
        ((spec.randomOracle u).run (L.get s) >>= fun r => (r.1, ·) <$> complete t r.2) := by
    simp only [StateLens.complete, StateLens.query, StateT.run, bind_map_left, map_bind,
      Functor.map_map, L.get_set, L.set_set]
  rw [lhs, rhs]
  exact (complete_query_swap t u (L.get s)).map _

/-- A simulation whose every query commutes with completions commutes with them. -/
theorem commutes_simulateQ {ι' : Type} {spec' : OracleSpec ι'} {σ α : Type} (L : CacheLens spec σ)
    (impl : QueryImpl spec' (StateT σ ProbComp)) (h : ∀ q, Commutes L (impl q)) (oa : OracleComp spec' α) :
    Commutes L (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact commutes_pure L a
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact commutes_bind L (h q) ih

/-- Completion of the outer focused cache equals completion of the inner one under the outer lens. -/
theorem complete_comp {σ ρ : Type} (E : StateLens σ ρ) (L : CacheLens spec ρ) (t : spec.Domain) (s : σ) :
    (E.comp L).complete t s = E.set s <$> L.complete t (E.get s) := by
  simp only [StateLens.complete, StateLens.comp, Functor.map_map]

/-- Commutation transports along an outer lens. -/
theorem commutes_lift {σ ρ α : Type} (E : StateLens σ ρ) (L : CacheLens spec ρ) (step : StateT ρ ProbComp α)
    (h : Commutes L step) : Commutes (E.comp L) (E.lift step) := by
  intro t s
  have lhs : (E.comp L).complete t s >>= (E.lift step).run =
      (fun r => (r.1, E.set s r.2)) <$> (L.complete t (E.get s) >>= step.run) := by
    rw [complete_comp]
    simp only [StateLens.lift, StateT.run, bind_map_left, map_bind, E.get_set, E.set_set]
  have rhs : ((E.lift step).run s >>= fun r => (r.1, ·) <$> (E.comp L).complete t r.2) =
      (fun r => (r.1, E.set s r.2)) <$> (step.run (E.get s) >>= fun r => (r.1, ·) <$> L.complete t r.2) := by
    simp only [complete_comp, StateLens.lift, StateT.run, bind_map_left, map_bind, Functor.map_map,
      E.get_set, E.set_set]
  rw [lhs, rhs]
  exact (h t (E.get s)).map _

/-- A continuation that keeps only a projection unchanged by the focused cache is blind. -/
theorem blind_proj {σ τ α : Type} (L : CacheLens spec σ) (proj : σ → τ)
    (proj_set : ∀ s c, proj (L.set s c) = proj s) :
    Blind L (fun r : α × σ => (pure (r.1, proj r.2) : ProbComp (α × τ))) := by
  intro a t s
  simp only [StateLens.complete, bind_map_left, proj_set]
  exact lawEq_drop _ _

/-- M4 glue: a step ending in a discarded call whose only state effect is a completion has the pointed form. -/
theorem factor_of_discard {σ α β I : Type} (L : CacheLens spec σ) (pre : StateT σ ProbComp (α × Option I))
    (call : I → StateT σ ProbComp β) (point : I → Option spec.Domain)
    (effect : ∀ i s, Prod.snd <$> (call i).run s = L.completeOpt (point i) s) (s : σ) :
    (pre >>= fun r => match r.2 with
      | none => pure r.1
      | some i => (fun _ => r.1) <$> call i).run s =
      ((pre.run s) >>= fun r => (r.1.1, ·) <$> L.completeOpt (r.1.2.bind point) r.2) := by
  rw [StateT.run_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨a, _ | i⟩, s'⟩
  · simp [StateLens.completeOpt]
  · simp only [Option.bind_some, StateT.run_map, ← effect i s', Functor.map_map]

/-- A completion followed by a commuting step and a blind continuation can be dropped. -/
theorem erase_tail {σ α γ : Type} (L : CacheLens spec σ) {step : StateT σ ProbComp α}
    (hstep : Commutes L step) {k : α × σ → ProbComp γ} (blind : Blind L k)
    (p : Option spec.Domain) (s : σ) :
    LawEq (L.completeOpt p s >>= fun s' => step.run s' >>= k) (step.run s >>= k) := by
  cases p with
  | none =>
      simp only [StateLens.completeOpt, pure_bind]
      exact LawEq.refl _
  | some t =>
      have first := LawEq.bind (hstep t s) (fun r => LawEq.refl (k r))
      have second : LawEq (step.run s >>= fun r => L.complete t r.2 >>= fun s' => k (r.1, s'))
          (step.run s >>= k) :=
        LawEq.bind (LawEq.refl _) (fun r => blind r.1 t r.2)
      simp only [StateLens.completeOpt]
      rw [← bind_assoc]
      refine first.trans ?_
      simpa only [bind_assoc, bind_map_left] using second

/-- Global erasure of discarded lazy queries (pointed form, M4). -/
theorem discard_erase {ι' : Type} {spec' : OracleSpec ι'} {σ α γ : Type} (L : CacheLens spec σ)
    (H : QueryImpl spec' (StateT σ ProbComp))
    (H₁ : (q : spec'.Domain) → StateT σ ProbComp (spec'.Range q × Option spec.Domain))
    (factor : ∀ q s, LawEq ((H q).run s) ((H₁ q).run s >>= fun r => (r.1.1, ·) <$> L.completeOpt r.1.2 r.2))
    (oblivious : ∀ q, Commutes L (Prod.fst <$> H₁ q))
    (k : α × σ → ProbComp γ) (blind : Blind L k) (oa : OracleComp spec' α) (s : σ) :
    LawEq ((simulateQ H oa).run s >>= k)
      ((simulateQ (fun q => Prod.fst <$> H₁ q : QueryImpl spec' (StateT σ ProbComp)) oa).run s >>= k) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => exact LawEq.refl _
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, bind_assoc]
      refine (LawEq.bind (factor q s) (fun r => LawEq.refl _)).trans ?_
      rw [StateT.run_map, bind_assoc, bind_map_left]
      refine LawEq.bind (LawEq.refl _) (fun r => ?_)
      rw [bind_map_left]
      refine (LawEq.bind (LawEq.refl _) (fun s' => ih r.1.1 s')).trans ?_
      exact erase_tail L (commutes_simulateQ L _ oblivious _) blind r.1.2 r.2

/-- `discard_erase` read through a projection that does not see the focused cache. -/
theorem discard_erase_proj {ι' : Type} {spec' : OracleSpec ι'} {σ τ α : Type} (L : CacheLens spec σ)
    (H : QueryImpl spec' (StateT σ ProbComp))
    (H₁ : (q : spec'.Domain) → StateT σ ProbComp (spec'.Range q × Option spec.Domain))
    (factor : ∀ q s, LawEq ((H q).run s) ((H₁ q).run s >>= fun r => (r.1.1, ·) <$> L.completeOpt r.1.2 r.2))
    (oblivious : ∀ q, Commutes L (Prod.fst <$> H₁ q))
    (proj : σ → τ) (proj_set : ∀ s c, proj (L.set s c) = proj s) (oa : OracleComp spec' α) (s : σ) :
    LawEq (Prod.map id proj <$> (simulateQ H oa).run s)
      (Prod.map id proj <$> (simulateQ (fun q => Prod.fst <$> H₁ q : QueryImpl spec' (StateT σ ProbComp)) oa).run s) := by
  have erased := discard_erase L H H₁ factor oblivious
    (fun r : α × σ => (pure (r.1, proj r.2) : ProbComp (α × τ))) (blind_proj L proj proj_set) oa s
  simpa only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq] using erased

/-- One step of the persistent lazy table, counts forgotten, is VCVio's lazy oracle (M8 bridge). -/
theorem impl_project (t : spec.Domain) (s : PqxdhRecordLiftLazyTable.State spec) :
    Prod.map id Prod.fst <$> (PqxdhRecordLiftLazyTable.impl (spec := spec) t).run s =
      (spec.randomOracle t).run s.1 := by
  simpa only [simulateQ_spec_query] using
    PqxdhRecordLiftLazyTable.run_project (spec := spec) (liftM (spec.query t)) s

end Cache
end BeaconcryptCore.Computational.LazyOracleDiscard

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.refl

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.symm

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.trans

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.of_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.of_eq

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.bind

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.map

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.evalDist_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.LawEq.evalDist_eq

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.lawEq_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.lawEq_swap

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.lawEq_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.lawEq_drop

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.complete_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.complete_run

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.complete_of_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.complete_of_none

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.complete_of_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.complete_of_some

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.query_of_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.query_of_none

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.query_of_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.query_of_some

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.complete_query_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.complete_query_swap

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.commutes_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.commutes_pure

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.commutes_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.commutes_bind

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.commutes_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.commutes_map

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.commutes_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.commutes_frame

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.commutes_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.commutes_query

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.commutes_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.commutes_simulateQ

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.complete_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.complete_comp

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.commutes_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.commutes_lift

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.blind_proj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.blind_proj

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.factor_of_discard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.factor_of_discard

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.erase_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.erase_tail

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.discard_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.discard_erase

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.discard_erase_proj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.discard_erase_proj

/--
info: 'BeaconcryptCore.Computational.LazyOracleDiscard.impl_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LazyOracleDiscard.impl_project
