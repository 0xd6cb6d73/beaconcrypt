import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnceTools

/-!
# Weighted query bounds through interpreter stacks (item 2, stage S8, generic tools)

This module is generic and contains no protocol code. Stage S8 bounds the random draws of the item 2 reductions, whose clients run the whole source program through several interpreters: the source client, the skeleton's native layer, the actual encapsulator, the KEM router, the CCA evaluation and the root client's public table. Each layer turns one request into a program whose cost depends on the kind of the request (one coin, a 64-byte table draw, a key-schedule or KEM operation). A weighted query bound carries such costs through the stack:

- `WBound work w n`: along every path of `work`, the weights `w` of its queries sum to at most `n`; a VCVio class bound `IsQueryBoundP` gives a weighted bound with weight `c` on the class (`wBound_of_isQueryBoundP`), and a weighted bound whose weight is at least one on a class gives the class bound (`isQueryBoundP_of_wBound`);
- rules for sequencing, mapping, monotonicity and sums of weights, and the bound of a program whose queries are classified by kind with a budget per kind (`wBound_kinds`);
- transport through stateless, stateful and optional stateful interpreters: if every step of the interpreter costs at most the weight of its request in the lower weights, the interpreted program costs at most the bound of the program (`wBound_simulate`, `wBound_run`, `wBound_option`).

These are structural facts; they charge nothing.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

/-! ### Weighted bounds -/

section Weighted

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-- Along every path of `work`, the weights of its queries sum to at most `n`. -/
def WBound (work : OracleComp spec α) (w : spec.Domain → ℕ) (n : ℕ) : Prop :=
  PFunctor.FreeM.rec (motive := fun _ => ℕ → Prop) (fun _ _ => True)
    (fun query _ ih budget => w query ≤ budget ∧ ∀ reply, ih reply (budget - w query)) work n

theorem wBound_pure (w : spec.Domain → ℕ) (value : α) (n : ℕ) : WBound (pure value : OracleComp spec α) w n := trivial

theorem wBound_query_bind (w : spec.Domain → ℕ) (query : spec.Domain) (next : spec.Range query → OracleComp spec α)
    (n : ℕ) :
    WBound (liftM (spec.query query) >>= next) w n ↔ w query ≤ n ∧ ∀ reply, WBound (next reply) w (n - w query) :=
  Iff.rfl

theorem wBound_mono {w : spec.Domain → ℕ} {work : OracleComp spec α} {n m : ℕ} (bounded : WBound work w n)
    (le : n ≤ m) : WBound work w m := by
  induction work using OracleComp.inductionOn generalizing n m with
  | pure value => trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at bounded ⊢
      exact ⟨bounded.1.trans le, fun reply => ih reply (bounded.2 reply) (by omega)⟩

theorem wBound_bind {w : spec.Domain → ℕ} {work : OracleComp spec α} {next : α → OracleComp spec β} {a b : ℕ}
    (first : WBound work w a) (rest : ∀ value ∈ support work, WBound (next value) w b) :
    WBound (work >>= next) w (a + b) := by
  induction work using OracleComp.inductionOn generalizing a with
  | pure value =>
      rw [pure_bind]
      exact wBound_mono (rest value (by simp)) (Nat.le_add_left _ _)
  | query_bind query cont ih =>
      rw [bind_assoc]
      rw [wBound_query_bind] at first ⊢
      refine ⟨first.1.trans (Nat.le_add_right _ _), fun reply => ?_⟩
      have := ih reply (first.2 reply) fun value member => rest value
        ((mem_support_bind_iff _ _ _).mpr ⟨reply, mem_support_query query reply, member⟩)
      exact wBound_mono this (by omega)

theorem wBound_map {w : spec.Domain → ℕ} {work : OracleComp spec α} (f : α → β) {n : ℕ} (bounded : WBound work w n) :
    WBound (f <$> work) w n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value =>
      rw [map_pure]
      trivial
  | query_bind query next ih =>
      rw [map_bind]
      rw [wBound_query_bind] at bounded ⊢
      exact ⟨bounded.1, fun reply => ih reply (bounded.2 reply)⟩

theorem wBound_map_iff {w : spec.Domain → ℕ} {work : OracleComp spec α} (f : α → β) {n : ℕ} :
    WBound (f <$> work) w n ↔ WBound work w n := by
  refine ⟨fun bounded => ?_, wBound_map f⟩
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => trivial
  | query_bind query next ih =>
      rw [map_bind] at bounded
      rw [wBound_query_bind] at bounded ⊢
      exact ⟨bounded.1, fun reply => ih reply (bounded.2 reply)⟩

theorem wBound_query (w : spec.Domain → ℕ) (query : spec.Domain) (n : ℕ) :
    WBound (liftM (spec.query query) : OracleComp spec (spec.Range query)) w n ↔ w query ≤ n := by
  have := wBound_query_bind w query (fun reply => (pure reply : OracleComp spec _)) n
  simp only [bind_pure] at this
  rw [this]
  exact ⟨fun bounded => bounded.1, fun le => ⟨le, fun _ => trivial⟩⟩

/-- Weights add up along every path. -/
theorem wBound_add {w₁ w₂ : spec.Domain → ℕ} {work : OracleComp spec α} {a b : ℕ}
    (first : WBound work w₁ a) (second : WBound work w₂ b) : WBound work (fun query => w₁ query + w₂ query) (a + b) := by
  induction work using OracleComp.inductionOn generalizing a b with
  | pure value => trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at first second ⊢
      refine ⟨Nat.add_le_add first.1 second.1, fun reply => ?_⟩
      exact wBound_mono (ih reply (first.2 reply) (second.2 reply)) (by omega)

/-- A weight pointwise below another is bounded by the other's bound. -/
theorem wBound_weight_mono {w₁ w₂ : spec.Domain → ℕ} (le : ∀ query, w₁ query ≤ w₂ query) {work : OracleComp spec α}
    {n : ℕ} (bounded : WBound work w₂ n) : WBound work w₁ n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at bounded ⊢
      exact ⟨(le query).trans bounded.1, fun reply => wBound_mono (ih reply (bounded.2 reply)) (by
        have := le query; omega)⟩

/-- A predicate-targeted query bound is a weighted bound with weight `c` on the targeted class. -/
theorem wBound_of_isQueryBoundP (p : spec.Domain → Prop) [DecidablePred p] (c : ℕ) {work : OracleComp spec α} {n : ℕ}
    (bounded : work.IsQueryBoundP p n) : WBound work (fun query => if p query then c else 0) (c * n) := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [wBound_query_bind]
      by_cases target : p query
      · have positive : 0 < n := bounded.1.resolve_left (not_not.mpr target)
        simp only [target, ite_true] at bounded ⊢
        refine ⟨Nat.le_mul_of_pos_right c positive, fun reply => ?_⟩
        have := ih reply (bounded.2 reply)
        rwa [Nat.mul_sub_one] at this
      · simp only [target, ite_false, Nat.sub_zero] at bounded ⊢
        exact ⟨Nat.zero_le _, fun reply => ih reply (bounded.2 reply)⟩

/-- A weighted bound with weight at least one on a class bounds the queries of the class. -/
theorem isQueryBoundP_of_wBound (p : spec.Domain → Prop) [DecidablePred p] {w : spec.Domain → ℕ}
    (heavy : ∀ query, p query → 1 ≤ w query) {work : OracleComp spec α} {n : ℕ} (bounded : WBound work w n) :
    work.IsQueryBoundP p n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at bounded
      rw [isQueryBoundP_query_bind_iff]
      by_cases target : p query
      · have := heavy query target
        refine ⟨Or.inr (by omega), fun reply => ?_⟩
        simp only [target, ite_true]
        exact ih reply (wBound_mono (bounded.2 reply) (by omega))
      · simp only [target, not_false_eq_true, true_or, ite_false, true_and]
        exact fun reply => ih reply (wBound_mono (bounded.2 reply) (by omega))

/-- Requests classified by kind, with a query budget per kind, bound the weight that charges each request the cost of its kind. -/
theorem wBound_kinds {Kind : Type} [Fintype Kind] [DecidableEq Kind] (classify : spec.Domain → Kind)
    (cost budget : Kind → ℕ) {work : OracleComp spec α}
    (bounded : ∀ kind, work.IsQueryBoundP (fun query => classify query = kind) (budget kind)) :
    WBound work (fun query => cost (classify query)) (∑ kind, cost kind * budget kind) := by
  have general : ∀ kinds : Finset Kind, WBound work
      (fun query => ∑ kind ∈ kinds, if classify query = kind then cost kind else 0)
      (∑ kind ∈ kinds, cost kind * budget kind) := by
    intro kinds
    induction kinds using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        induction work using OracleComp.inductionOn with
        | pure value => trivial
        | query_bind query next ih => exact (wBound_query_bind _ _ _ _).mpr ⟨le_rfl, fun reply => ih reply
            (fun kind => (isQueryBoundP_query_bind_iff _ _ _ _ |>.mp (bounded kind)).2 reply |>.mono (by
              split <;> omega))⟩
    | insert kind kinds fresh ih =>
        simp only [Finset.sum_insert fresh]
        exact wBound_add (wBound_of_isQueryBoundP _ (cost kind) (bounded kind)) ih
  have all := general Finset.univ
  refine wBound_weight_mono (fun query => ?_) all
  rw [Finset.sum_eq_single (classify query)]
  · simp
  · intro kind _ other
    simp [Ne.symm other]
  · simp

end Weighted

/-! ### Transport through interpreters -/

section Transport

variable {ι ι' σ α : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}

/-- A stateless interpreter whose every step costs at most the weight of its request. -/
theorem wBound_simulate (handler : QueryImpl spec (OracleComp spec')) (w : spec.Domain → ℕ) (w' : spec'.Domain → ℕ)
    (step : ∀ query, WBound (handler query) w' (w query)) {work : OracleComp spec α} {n : ℕ}
    (bounded : WBound work w n) : WBound (simulateQ handler work) w' n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query]
      have := wBound_bind (step query) (b := n - w query) fun reply _ => ih reply (bounded.2 reply)
      exact wBound_mono this (by have := bounded.1; omega)

/-- A stateful interpreter whose every step costs at most the weight of its request. -/
theorem wBound_run (handler : QueryImpl spec (StateT σ (OracleComp spec'))) (w : spec.Domain → ℕ)
    (w' : spec'.Domain → ℕ) (step : ∀ query state, WBound ((handler query).run state) w' (w query))
    {work : OracleComp spec α} {n : ℕ} (bounded : WBound work w n) (state : σ) :
    WBound ((simulateQ handler work).run state) w' n := by
  induction work using OracleComp.inductionOn generalizing n state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have := wBound_bind (step query state) (b := n - w query) fun result _ =>
        ih result.1 (bounded.2 result.1) result.2
      exact wBound_mono this (by have := bounded.1; omega)

/-- An optional stateful interpreter whose every step costs at most the weight of its request. -/
theorem wBound_option (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec')))) (w : spec.Domain → ℕ)
    (w' : spec'.Domain → ℕ) (step : ∀ query state, WBound (((handler query).run).run state) w' (w query))
    {work : OracleComp spec α} {n : ℕ} (bounded : WBound work w n) (state : σ) :
    WBound (((simulateQ handler work).run).run state) w' n := by
  induction work using OracleComp.inductionOn generalizing n state with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure]
      trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at bounded
      rw [PqxdhRegistrationJointBeaconFinishOnce.option_run_bind]
      refine wBound_mono (wBound_bind (step query state) (b := n - w query) ?_) (by have := bounded.1; omega)
      intro result _
      rcases result with ⟨_ | reply, after⟩
      · trivial
      · exact ih reply (bounded.2 reply) after

end Transport

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_query_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_map_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_map_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_add

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_weight_mono' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_weight_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_of_isQueryBoundP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_of_isQueryBoundP

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.isQueryBoundP_of_wBound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.isQueryBoundP_of_wBound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_kinds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_kinds

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_simulate

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_option' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_option
