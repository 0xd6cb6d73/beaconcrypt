import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

/-!
# Read accounting for the random-oracle split (item 2, stage S1c, tools)

Stage S1c applies G1 (`PqxdhExtractRomHiddenSuffix.hidden_suffix_bound`) to the shared world of stage S1b. G1 needs, for every outcome of the prefix, a finite set of byte strings that covers the keys of the table cache at the cut, and a bound on the direct table reads of the client after the cut, whose sum is at most one budget `Q` (the plan's cut-split of the source budget, which gives coefficient one). This module contains the generic accounting tools:

- `potential_run`: a potential on the state of a handler that grows by at most one on every targeted query grows by at most the query bound of the program;
- `scan_potential`: the same along the scan of a source program up to a selected raw accept (`PqxdhRegistrationJointAcceptCut.scan`), together with the remaining bound of the suspended continuation, so that the reads before the cut and the queries after it share one budget;
- `isQueryBoundP_or`: query bounds for two predicates add up for their disjunction;
- `isQueryBoundP_option_of_step`: query bounds transported through an optional stateful interpreter;
- `cacheKeys` and `randomOracle_keys`: one read of the lazily sampled table adds at most its own key to the cache.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

open PqxdhSecretInputKdf (HmacBlock HmacOracle)

/-! ### Potentials and query bounds -/

section Generic

variable {ι ι' σ α : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- A potential that grows by at most one on every targeted query, and not at all on other queries, grows by at most the program's query bound. -/
theorem potential_run (handler : QueryImpl spec (StateT σ (OracleComp spec'))) (potential : σ → ℕ∞)
    (p : ι → Prop) [DecidablePred p]
    (step : ∀ query state, ∀ result ∈ support ((handler query).run state),
      potential result.2 ≤ potential state + ((if p query then 1 else 0 : ℕ) : ℕ∞))
    (work : OracleComp spec α) (n : ℕ) (bounded : work.IsQueryBoundP p n) (state : σ) :
    ∀ result ∈ support ((simulateQ handler work).run state), potential result.2 ≤ potential state + n := by
  induction work using OracleComp.inductionOn generalizing n state with
  | pure value =>
      intro result reached
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact le_self_add
  | query_bind query next ih =>
      intro result reached
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, rest⟩ := reached
      have later := ih middle.1 _ (bounded.2 middle.1) middle.2 result rest
      have now := step query state middle first
      by_cases target : p query
      · have positive : 0 < n := bounded.1.resolve_left (not_not.mpr target)
        simp only [target, ite_true, Nat.cast_one] at later now
        calc potential result.2 ≤ potential middle.2 + ((n - 1 : ℕ) : ℕ∞) := later
          _ ≤ potential state + 1 + ((n - 1 : ℕ) : ℕ∞) := add_le_add now le_rfl
          _ = potential state + n := by
            rw [add_assoc]
            congr 1
            rw [← Nat.cast_one, ← Nat.cast_add]
            congr 1
            omega
      · simp only [target, ite_false, Nat.cast_zero, add_zero] at later now
        exact later.trans (add_le_add now le_rfl)

/-- Query bounds for two predicates add up for their disjunction. -/
theorem isQueryBoundP_or (work : OracleComp spec α) {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    {n m : ℕ} (first : work.IsQueryBoundP p n) (second : work.IsQueryBoundP q m) :
    work.IsQueryBoundP (fun query => p query ∨ q query) (n + m) := by
  induction work using OracleComp.inductionOn generalizing n m with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at first second ⊢
      refine ⟨?_, fun reply => ?_⟩
      · by_cases hp : p query
        · exact Or.inr (Nat.lt_of_lt_of_le (first.1.resolve_left (not_not.mpr hp)) (Nat.le_add_right _ _))
        · by_cases hq : q query
          · exact Or.inr (Nat.lt_of_lt_of_le (second.1.resolve_left (not_not.mpr hq)) (Nat.le_add_left _ _))
          · exact Or.inl (by simp [hp, hq])
      · refine (ih reply (first.2 reply) (second.2 reply)).mono ?_
        have nonzero₁ : p query → 0 < n := fun hp => first.1.resolve_left (not_not.mpr hp)
        have nonzero₂ : q query → 0 < m := fun hq => second.1.resolve_left (not_not.mpr hq)
        by_cases hp : p query <;> by_cases hq : q query
        · have := nonzero₁ hp
          have := nonzero₂ hq
          simp only [hp, hq, or_self, ite_true]
          omega
        · have := nonzero₁ hp
          simp only [hp, hq, or_false, ite_true, ite_false]
          omega
        · have := nonzero₂ hq
          simp only [hp, hq, false_or, ite_true, ite_false]
          omega
        · simp only [hp, hq, or_self, ite_false, le_refl]

/-- Query bounds pass through an optional stateful interpreter whose every step makes at most one targeted query on a targeted source query and none otherwise. -/
theorem isQueryBoundP_option_of_step {J : Type} (handler : QueryImpl spec (OptionT (StateT J (OracleComp spec'))))
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    (work : OracleComp spec α) (n : ℕ) (bounded : work.IsQueryBoundP p n)
    (step : ∀ query state, (((handler query).run).run state).IsQueryBoundP q (if p query then 1 else 0))
    (state : J) : (((simulateQ handler work).run).run state).IsQueryBoundP q n := by
  induction work using OracleComp.inductionOn generalizing n state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      refine (isQueryBoundP_bind (step query state) (m := if p query then n - 1 else n) fun result _ => ?_).mono ?_
      · rcases result with ⟨_ | reply, after⟩
        · trivial
        · exact ih reply _ (bounded.2 reply) after
      · by_cases target : p query
        · have := bounded.1.resolve_left (not_not.mpr target)
          simp only [target, ite_true]
          omega
        · simp [target]

end Generic

/-! ### Keys of the table cache -/

section Keys

/-- The keys of a table cache. -/
def cacheKeys (cache : HmacOracle.QueryCache) : Set Pqxdh.Bytes := {point | cache point ≠ none}

theorem cacheKeys_empty : cacheKeys (∅ : HmacOracle.QueryCache) = ∅ := by
  ext point
  simp [cacheKeys]

/-- One read of the lazily sampled table adds at most its own key. -/
theorem randomOracle_keys (point : Pqxdh.Bytes) (cache : HmacOracle.QueryCache) :
    ∀ result ∈ support ((HmacOracle.randomOracle point).run cache),
      cacheKeys result.2 ⊆ insert point (cacheKeys cache) := by
  intro result reached
  rw [randomOracle.run_eq] at reached
  cases found : cache point with
  | some value =>
      simp only [found, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact Set.subset_insert _ _
  | none =>
      simp only [found, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
      obtain ⟨value, _, rfl⟩ := reached
      intro other member
      by_cases same : other = point
      · exact Or.inl same
      · refine Or.inr ?_
        simpa [cacheKeys, QueryCache.cacheQuery, Function.update_of_ne same] using member

/-- One read of the lazily sampled table grows the number of keys by at most one. -/
theorem randomOracle_encard (point : Pqxdh.Bytes) (cache : HmacOracle.QueryCache) :
    ∀ result ∈ support ((HmacOracle.randomOracle point).run cache),
      (cacheKeys result.2).encard ≤ (cacheKeys cache).encard + 1 := by
  intro result reached
  exact (Set.encard_le_encard (randomOracle_keys point cache result reached)).trans (Set.encard_insert_le _ _)

end Keys

/-! ### The cut-split along the scan to the selected raw accept -/

section Scan

open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan)

variable {KemSK Result σ ι' : Type} {spec' : OracleSpec ι'}

/-- The source requests that read the shared table: raw accepts, Beacon finishes and public HMAC. -/
def TableKind : (Spec KemSK).Domain → Prop
  | .inl (.inr (.accept _)) => True
  | .inl (.inr (.finish _ _)) => True
  | .inl (.inr (.hmac _ _)) => True
  | _ => False

instance : DecidablePred (TableKind (KemSK := KemSK))
  | .inl (.inl _) => inferInstanceAs (Decidable False)
  | .inl (.inr (.create _ _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.bundle _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.accept _)) => inferInstanceAs (Decidable True)
  | .inl (.inr (.build _ _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.finish _ _)) => inferInstanceAs (Decidable True)
  | .inl (.inr (.hmac _ _)) => inferInstanceAs (Decidable True)
  | .inl (.inr (.hash _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.reveal _)) => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable False)

/-- One forwarded request of the scan: the potential and the remaining bound of the continuation move together. -/
theorem scan_forward (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec'))) (potential : σ → ℕ∞)
    (step : ∀ query state, ∀ result ∈ support ((handler query).run state),
      potential result.2 ≤ potential state + ((if TableKind query then 1 else 0 : ℕ) : ℕ∞))
    (query : (Spec KemSK).Domain) (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (n : ℕ)
    (bounded : (liftM ((Spec KemSK).query query) >>= next : OracleComp (Spec KemSK) Result).IsQueryBoundP (TableKind (KemSK := KemSK)) n)
    (index : Nat) (state : σ)
    (ih : ∀ reply (n : ℕ), (next reply).IsQueryBoundP (TableKind (KemSK := KemSK)) n → ∀ state,
      ∀ result ∈ support ((simulateQ handler (scan (next reply) index)).run state), ∀ raw rest,
        result.1 = .pending raw rest → ∃ c : ℕ, potential result.2 ≤ potential state + c ∧ c + 1 ≤ n ∧
          ∀ reply, (rest reply).IsQueryBoundP (TableKind (KemSK := KemSK)) (n - c - 1)) :
    ∀ result ∈ support ((simulateQ handler (liftM ((Spec KemSK).query query) >>= fun reply =>
        scan (next reply) index)).run state), ∀ raw rest,
      result.1 = .pending raw rest → ∃ c : ℕ, potential result.2 ≤ potential state + c ∧ c + 1 ≤ n ∧
        ∀ reply, (rest reply).IsQueryBoundP (TableKind (KemSK := KemSK)) (n - c - 1) := by
  intro result reached raw rest pending
  rw [isQueryBoundP_query_bind_iff] at bounded
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨middle, first, later⟩ := reached
  obtain ⟨c, growth, room, remaining⟩ := ih middle.1 _ (bounded.2 middle.1) middle.2 result later raw rest pending
  have now := step query state middle first
  by_cases target : TableKind query
  · have positive : 0 < n := bounded.1.resolve_left (not_not.mpr target)
    simp only [target, ite_true, Nat.cast_one] at room remaining now
    refine ⟨c + 1, ?_, by omega, fun reply => (remaining reply).mono (by omega)⟩
    calc potential result.2 ≤ potential middle.2 + c := growth
      _ ≤ potential state + 1 + c := add_le_add now le_rfl
      _ = potential state + ((c + 1 : ℕ) : ℕ∞) := by
        rw [add_assoc, Nat.cast_add, Nat.cast_one, add_comm (1 : ℕ∞)]
  · simp only [target, ite_false, Nat.cast_zero, add_zero] at room remaining now
    exact ⟨c, growth.trans (add_le_add now le_rfl), room, remaining⟩

/-- The cut-split along the scan to the selected raw accept: the potential at the cut has grown by at most `c`, the cut's accept and the `c` table requests before it fit the budget, and the suspended continuation keeps the rest of it. -/
theorem scan_potential (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec'))) (potential : σ → ℕ∞)
    (step : ∀ query state, ∀ result ∈ support ((handler query).run state),
      potential result.2 ≤ potential state + ((if TableKind query then 1 else 0 : ℕ) : ℕ∞))
    (work : OracleComp (Spec KemSK) Result) (n : ℕ) (bounded : work.IsQueryBoundP (TableKind (KemSK := KemSK)) n) (index : Nat)
    (state : σ) :
    ∀ result ∈ support ((simulateQ handler (scan work index)).run state), ∀ raw next,
      result.1 = .pending raw next → ∃ c : ℕ, potential result.2 ≤ potential state + c ∧ c + 1 ≤ n ∧
        ∀ reply, (next reply).IsQueryBoundP (TableKind (KemSK := KemSK)) (n - c - 1) := by
  induction work using OracleComp.inductionOn generalizing index n state with
  | pure value =>
      intro result reached raw next pending
      change result ∈ support ((simulateQ handler (pure (Cut.complete value) : OracleComp (Spec KemSK) _)).run state)
        at reached
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      cases pending
  | query_bind query next ih =>
      rcases query with (coin | request) | read
      · exact scan_forward handler potential step _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)
      · cases request with
        | accept raw =>
            cases index with
            | zero =>
                intro result reached raw' rest pending
                change result ∈ support ((simulateQ handler (pure (Cut.pending raw next) :
                  OracleComp (Spec KemSK) _)).run state) at reached
                simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
                subst reached
                cases pending
                rw [isQueryBoundP_query_bind_iff] at bounded
                have positive : 0 < n := bounded.1.resolve_left (not_not.mpr trivial)
                refine ⟨0, by simp, by omega, fun reply => ?_⟩
                have later := bounded.2 reply
                rw [ite_eq_left (show TableKind (KemSK := KemSK) (.inl (.inr (.accept raw))) from trivial)] at later
                simpa using later
            | succ index =>
                exact scan_forward handler potential step _ next n bounded index state
                  (fun reply n bounded state => ih reply n bounded index state)
        | _ =>
            exact scan_forward handler potential step _ next n bounded index state
              (fun reply n bounded state => ih reply n bounded index state)
      · exact scan_forward handler potential step _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)

end Scan

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.potential_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.potential_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.isQueryBoundP_or' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.isQueryBoundP_or

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.isQueryBoundP_option_of_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.isQueryBoundP_option_of_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.cacheKeys_empty' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.cacheKeys_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.randomOracle_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.randomOracle_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.randomOracle_encard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.randomOracle_encard

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.scan_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.scan_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.scan_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.scan_potential
