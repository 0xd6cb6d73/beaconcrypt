import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonTools
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Potential query bounds through optional stateful interpreters (item 2, stage T, generic tools)

This module is generic and contains no protocol code. Stage T bounds the hidden reads of the item 2 root client by 2, which needs a bound that depends on the state of several interpreter layers at once: a Beacon owner's KEM creation index lives in the state of the top-level client, while the creation counter that hands these indices out lives in the state of the KEM router several layers below. The tools here collapse such a stack into one optional stateful interpreter and bound its targeted queries by a potential on the joint state.

- `PotBound work p f n`: along every path of `work`, the number of `p`-queries plus `f` of the final value is at most `n`. It is the potential form of VCVio's `IsQueryBoundP` (`isQueryBoundP_of_potBound`), with the rules `potBound_pure`, `potBound_query_bind`, `potBound_mono`, `potBound_bind` and `potBound_of_bound` (a query bound together with a bound on the final values).
- `option_potential`: if every step of an optional stateful interpreter, from a state satisfying an invariant, makes at most as many targeted queries as the potential `Φ` drops (a stopped step ends with potential 0), then so does every program.
- `composeOpt` and `composeOpt_run`: a stateful interpreter followed by an optional stateful interpreter is one optional stateful interpreter on the product state.
- `simulate_support`, `run_support`, `option_support`, `option_monotone`, `option_invariant`: interpreted programs have no outputs the program cannot produce, a measure that no step of an optional stateful interpreter decreases is not decreased by any program, and a state predicate that every step keeps is kept by every program; `option_simulate_bind` unfolds a run on a sequential composition.

These are program equalities and structural facts; they charge nothing.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-! ### Potential bounds -/

section Potential

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-- Along every path of `work`, the number of `p`-queries plus `f` of the final value is at most `n`: the budget `n` decreases by one on every `p`-query, must be positive before it, and must cover `f` of the final value. -/
def PotBound (work : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (f : α → ℕ) (n : ℕ) : Prop :=
  PFunctor.FreeM.rec (motive := fun _ => ℕ → Prop) (fun value budget => f value ≤ budget)
    (fun query _ ih budget => (¬ p query ∨ 0 < budget) ∧ ∀ reply, ih reply (if p query then budget - 1 else budget))
    work n

variable (p : ι → Prop) [DecidablePred p]

theorem potBound_pure (f : α → ℕ) (value : α) (n : ℕ) :
    PotBound (pure value : OracleComp spec α) p f n ↔ f value ≤ n := Iff.rfl

theorem potBound_query_bind (f : α → ℕ) (query : spec.Domain) (next : spec.Range query → OracleComp spec α) (n : ℕ) :
    PotBound (liftM (spec.query query) >>= next) p f n ↔
      (¬ p query ∨ 0 < n) ∧ ∀ reply, PotBound (next reply) p f (if p query then n - 1 else n) := Iff.rfl

variable {p}

theorem potBound_mono {f : α → ℕ} {work : OracleComp spec α} {n m : ℕ} (bounded : PotBound work p f n) (le : n ≤ m) :
    PotBound work p f m := by
  induction work using OracleComp.inductionOn generalizing n m with
  | pure value => exact (potBound_pure p f value n).mp bounded |>.trans le
  | query_bind query next ih =>
      rw [potBound_query_bind] at bounded ⊢
      refine ⟨bounded.1.imp id fun positive => Nat.lt_of_lt_of_le positive le, fun reply => ih reply (bounded.2 reply) ?_⟩
      split <;> omega

/-- A potential bound implies the query bound at the initial budget. -/
theorem isQueryBoundP_of_potBound {f : α → ℕ} {work : OracleComp spec α} {n : ℕ} (bounded : PotBound work p f n) :
    work.IsQueryBoundP p n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => trivial
  | query_bind query next ih =>
      rw [potBound_query_bind] at bounded
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply (bounded.2 reply)⟩

/-- Sequential composition: the continuation from a final value `a` of the first part has the budget `g a` that the first part leaves for it. -/
theorem potBound_bind {g : α → ℕ} {f : β → ℕ} {work : OracleComp spec α} {next : α → OracleComp spec β} {n : ℕ}
    (first : PotBound work p g n) (rest : ∀ value ∈ support work, PotBound (next value) p f (g value)) :
    PotBound (work >>= next) p f n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value =>
      rw [pure_bind]
      exact potBound_mono (rest value (by simp)) ((potBound_pure p g value n).mp first)
  | query_bind query cont ih =>
      rw [bind_assoc]
      rw [potBound_query_bind] at first ⊢
      refine ⟨first.1, fun reply => ih reply (first.2 reply) fun value member => rest value ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, member⟩

/-- A query bound `d` together with a bound `f a + d ≤ n` on every final value gives the potential bound `n`. -/
theorem potBound_of_bound {f : α → ℕ} {work : OracleComp spec α} {d n : ℕ} (bounded : work.IsQueryBoundP p d)
    (le : d ≤ n) (final : ∀ value ∈ support work, f value + d ≤ n) : PotBound work p f n := by
  induction work using OracleComp.inductionOn generalizing d n with
  | pure value => exact (potBound_pure p f value n).mpr (by have := final value (by simp); omega)
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [potBound_query_bind]
      refine ⟨bounded.1.imp id fun positive => Nat.lt_of_lt_of_le positive le, fun reply => ?_⟩
      have member : ∀ value ∈ support (next reply), value ∈ support (liftM (spec.query query) >>= next) :=
        fun value member => (mem_support_bind_iff _ _ _).mpr ⟨reply, mem_support_query query reply, member⟩
      by_cases target : p query
      · have positive : 0 < d := bounded.1.resolve_left (not_not.mpr target)
        simp only [target, ite_true] at bounded ⊢
        exact ih reply (bounded.2 reply) (by omega) fun value reached => by
          have := final value (member value reached); omega
      · simp only [target, ite_false] at bounded ⊢
        exact ih reply (bounded.2 reply) le fun value reached => final value (member value reached)

/-- A program without targeted queries whose final values all have potential at most `n`. -/
theorem potBound_of_free {f : α → ℕ} {work : OracleComp spec α} {n : ℕ} (free : work.IsQueryBoundP p 0)
    (final : ∀ value ∈ support work, f value ≤ n) : PotBound work p f n :=
  potBound_of_bound free (Nat.zero_le n) fun value member => by simpa using final value member

theorem potBound_map {f : β → ℕ} {work : OracleComp spec α} (g : α → β) {n : ℕ} (bounded : PotBound work p (f ∘ g) n) :
    PotBound (g <$> work) p f n := by
  rw [map_eq_bind_pure_comp]
  exact potBound_bind bounded fun value _ => (potBound_pure p f (g value) _).mpr le_rfl

end Potential

/-! ### Optional stateful interpreters -/

section Option

variable {ι ι' σ α : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}

/-- The potential of a run of an optional stateful interpreter: `Φ` of the final state, and 0 for a stopped run. -/
def optPot (Φ : σ → ℕ) {β : Type} (result : Option β × σ) : ℕ :=
  match result.1 with
  | none => 0
  | some _ => Φ result.2

/-- One step of a run of an optional stateful interpreter, followed by the rest. -/
theorem option_run_bind (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec'))))
    (query : spec.Domain) (next : spec.Range query → OracleComp spec α) (state : σ) :
    ((simulateQ handler (liftM (spec.query query) >>= next)).run).run state =
      (((handler query).run).run state >>= fun result => match result.1 with
        | none => pure (none, result.2)
        | some reply => ((simulateQ handler (next reply)).run).run result.2) := by
  simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply bind_congr
  rintro ⟨_ | reply, after⟩ <;> rfl

/-- A run of an optional stateful interpreter on a sequential composition: the first part, then the rest unless it stopped. -/
theorem option_simulate_bind {β : Type} (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec'))))
    (work : OracleComp spec α) (next : α → OracleComp spec β) (state : σ) :
    ((simulateQ handler (work >>= next)).run).run state =
      (((simulateQ handler work).run).run state >>= fun result => match result.1 with
        | none => pure (none, result.2)
        | some value => ((simulateQ handler (next value)).run).run result.2) := by
  simp only [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply bind_congr
  rintro ⟨_ | value, after⟩ <;> rfl

/-- A predicate on the state that every step keeps is kept by every program. -/
theorem option_invariant (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec')))) (inv : σ → Prop)
    (step : ∀ query state, inv state → ∀ result ∈ support (((handler query).run).run state), inv result.2)
    (work : OracleComp spec α) (state : σ) (holds : inv state) :
    ∀ result ∈ support (((simulateQ handler work).run).run state), inv result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member]
      exact holds
  | query_bind query next ih =>
      intro result member
      rw [option_run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, first, rest⟩ := member
      rcases middle with ⟨_ | reply, after⟩
      · simp only [support_pure, Set.mem_singleton_iff] at rest
        rw [rest]
        exact step query state holds _ first
      · exact ih reply after (step query state holds _ first) result rest

/-- Potential bound for an optional stateful interpreter: if every step from a state satisfying `inv` makes at most as many targeted queries as the potential drops, with potential 0 after a stop, and keeps `inv`, then every program does. -/
theorem option_potential (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec'))))
    (p : ι' → Prop) [DecidablePred p] (Φ : σ → ℕ) (inv : σ → Prop)
    (step : ∀ query state, inv state → PotBound (((handler query).run).run state) p (optPot Φ) (Φ state))
    (keep : ∀ query state, inv state → ∀ result ∈ support (((handler query).run).run state), ∀ reply,
      result.1 = some reply → inv result.2)
    (work : OracleComp spec α) (state : σ) (holds : inv state) :
    PotBound (((simulateQ handler work).run).run state) p (optPot Φ) (Φ state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure]
      exact (potBound_pure p _ _ _).mpr le_rfl
  | query_bind query next ih =>
      rw [option_run_bind]
      refine potBound_bind (step query state holds) fun result member => ?_
      rcases result with ⟨_ | reply, after⟩
      · exact (potBound_pure p _ _ _).mpr (by simp [optPot])
      · exact ih reply after (keep query state holds _ member reply rfl)

/-- A measure that no step decreases is not decreased by any program. -/
theorem option_monotone (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec')))) (μ : σ → ℕ)
    (step : ∀ query state, ∀ result ∈ support (((handler query).run).run state), μ state ≤ μ result.2)
    (work : OracleComp spec α) (state : σ) :
    ∀ result ∈ support (((simulateQ handler work).run).run state), μ state ≤ μ result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member]
  | query_bind query next ih =>
      intro result member
      rw [option_run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, first, rest⟩ := member
      rcases middle with ⟨_ | reply, after⟩
      · simp only [support_pure, Set.mem_singleton_iff] at rest
        rw [rest]
        exact step query state _ first
      · exact (step query state _ first).trans (ih reply after result rest)

/-- Interpreting a program by a stateless interpreter adds no outputs. -/
theorem simulate_support (handler : QueryImpl spec (OracleComp spec')) (work : OracleComp spec α) :
    support (simulateQ handler work) ⊆ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      intro result member
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at member
      obtain ⟨reply, -, member⟩ := member
      exact (mem_support_bind_iff _ _ _).mpr ⟨reply, mem_support_query query reply, ih reply member⟩

/-- Every output of an interpreted stateful run is an output of the program. -/
theorem run_support (handler : QueryImpl spec (StateT σ (OracleComp spec'))) (work : OracleComp spec α) (state : σ) :
    ∀ result ∈ support ((simulateQ handler work).run state), result.1 ∈ support work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member]
      simp
  | query_bind query next ih =>
      intro result member
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, -, rest⟩ := member
      exact (mem_support_bind_iff _ _ _).mpr ⟨middle.1, mem_support_query query middle.1, ih middle.1 middle.2 result rest⟩

/-- Every output of an interpreted optional stateful run that did not stop is an output of the program. -/
theorem option_support (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec')))) (work : OracleComp spec α)
    (state : σ) : ∀ result ∈ support (((simulateQ handler work).run).run state), ∀ value,
      result.1 = some value → value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result member found reached
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member] at reached
      cases reached
      simp
  | query_bind query next ih =>
      intro result member found reached
      rw [option_run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, -, rest⟩ := member
      rcases middle with ⟨_ | reply, after⟩
      · simp only [support_pure, Set.mem_singleton_iff] at rest
        rw [rest] at reached
        cases reached
      · exact (mem_support_bind_iff _ _ _).mpr ⟨reply, mem_support_query query reply, ih reply after result rest found
          reached⟩

end Option

/-! ### Lifting a single query into a sum interface -/

section Lift

/-- Lifting a query into the left summand of a sum interface is that summand's query. -/
theorem liftComp_inl {ιA ιT : Type} {A : OracleSpec.{0, 0} ιA} {T : OracleSpec.{0, 0} ιT} (query : ιA) :
    (liftM (A.query query) : OracleComp A (A.Range query)).liftComp (A + T) =
      (liftM ((A + T).query (.inl query)) : OracleComp (A + T) (A.Range query)) := rfl

end Lift

/-! ### Collapsing a stateful interpreter onto an optional stateful interpreter -/

section Compose

variable {ιE ιM ιB S J α : Type} {E : OracleSpec.{0, 0} ιE} {M : OracleSpec.{0, 0} ιM} {B : OracleSpec.{0, 0} ιB}

/-- A stateful interpreter `top` followed by an optional stateful interpreter `low`, as one optional stateful interpreter on the product state. A stopped step keeps the state of `top` from before the step. -/
def composeOpt (top : QueryImpl E (StateT S (OracleComp M))) (low : QueryImpl M (OptionT (StateT J (OracleComp B)))) :
    QueryImpl E (OptionT (StateT (S × J) (OracleComp B))) :=
  fun query => OptionT.mk (StateT.mk fun state =>
    (fun result => (result.1.map Prod.fst, ((result.1.map Prod.snd).getD state.1, result.2))) <$>
      ((simulateQ low ((top query).run state.1)).run).run state.2)

theorem composeOpt_step (top : QueryImpl E (StateT S (OracleComp M)))
    (low : QueryImpl M (OptionT (StateT J (OracleComp B)))) (query : ιE) (state : S × J) :
    (((composeOpt top low query).run).run state) =
      (fun result => (result.1.map Prod.fst, ((result.1.map Prod.snd).getD state.1, result.2))) <$>
        ((simulateQ low ((top query).run state.1)).run).run state.2 := rfl

/-- The layered run is the collapsed run, with the final state of `top` moved into the result. -/
theorem composeOpt_run (top : QueryImpl E (StateT S (OracleComp M)))
    (low : QueryImpl M (OptionT (StateT J (OracleComp B)))) (work : OracleComp E α) (state : S) (lower : J) :
    ((simulateQ low ((simulateQ top work).run state)).run).run lower =
      (fun result => (result.1.map fun value => (value, result.2.1), result.2.2)) <$>
        ((simulateQ (composeOpt top low) work).run).run (state, lower) := by
  induction work using OracleComp.inductionOn generalizing state lower with
  | pure value => simp
  | query_bind query next ih =>
      rw [option_run_bind, composeOpt_step]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OptionT.run_bind, Option.elimM, map_bind,
        bind_map_left]
      apply bind_congr
      rintro ⟨_ | ⟨reply, after⟩, below⟩
      · simp
      · exact ih reply after below

end Compose

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_query_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_mono' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.isQueryBoundP_of_potBound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.isQueryBoundP_of_potBound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_of_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_of_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_of_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_of_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.potBound_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_run_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_run_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_simulate_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_simulate_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_invariant' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_potential

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_monotone' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_monotone

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.simulate_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.simulate_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.run_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.run_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.liftComp_inl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.liftComp_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.composeOpt_step' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.composeOpt_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.composeOpt_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.composeOpt_run
