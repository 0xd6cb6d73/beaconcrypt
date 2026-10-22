import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor
import BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable
import BeaconcryptCore.Computational.PqxdhRecordLiftInterface
import BeaconcryptCore.Computational.LazyOracleDiscard

/-!
# Indexed lazy tables and the first-touch slot allocator (item 2, stage S7, generic tables)

This module is generic and contains no protocol code. It provides the tables of stage S7 of the item 2 plan, which makes every hidden entry ideal, one entry at a time, in first-touch order.

- `indexedImpl sampler` is a lazily sampled table whose `j`-th fresh point (in first-touch order) is drawn from `sampler j`; repeated points are answered from the table. `indexed_eager` draws the `k`-th fresh value before the run (`pin k value sampler` answers the `k`-th fresh point with `value`), by `PqxdhServerAuthEntryFactor.eager_run`. It is a distribution equality; no value is programmed. It is stated as an equality in distribution (`EvalDistEq`), like that lemma; `indexed_eager_output` restates it for the client's output in the measure notation `𝒟[…]`.
- `firstTable_pinned`: the first-value table of stage S3b (`PqxdhRegistrationJointKemEntryFactor.firstTable`) is the indexed table pinned at its first fresh point.
- `indexed_lazy`: a client with at most `m` value requests, run from a table with fewer than `q - m` fresh points, sees only the first `q` samplers; if these are uniform, the indexed table is VCVio's lazy uniform table.
- `slotImpl service` puts a first-touch coordinate-to-slot allocator in front of a slot service (item 2 plan section 20, note 2): a new point gets the next free slot of `PqxdhRecordLiftInterface.Slot n`, a repeated point keeps its slot, and the slot's value is read only through `service`. `slot_lazy` shows that with `service` the persistent lazy table `PqxdhRecordLiftLazyTable.impl` and at most `n` value requests, the allocator and table are VCVio's lazy uniform table on the points. `slot_natural` is an exact-form naturality for clients of the allocator: a client reads slot values only through the slot service, so a projection that carries each step of one slot service to the corresponding step of another by an exact program equality under an invariant (for example `LazyOracleDiscard.impl_project`, which carries `tableService` to VCVio's lazy oracle on the slots) carries the whole run. It is item 2's exact-form analogue of the property that the common experiment (CE-11) calls `CoreNatural`, not that property: `CoreNatural` takes service projections in law (`LawEq`), which the split service of CE-11 needs because drawing material and seed and joining them is a different program from one uniform 108-byte draw, and it concerns CE-11's per-command registration core. CE-11b still has to prove `CoreNatural` for its own core; a `LawEq` variant of `slot_natural` would be the reusable piece.

These are program and distribution equalities; they charge nothing.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry

section Indexed

variable {D R : Type} [DecidableEq D]

/-- A client of coins and of value requests at points of `D`. -/
abbrev Spec (D R : Type) := unifSpec + (D →ₒ R)

/-- The table state with the number of fresh points so far. -/
abbrev IState (D R : Type) := (D →ₒ R).QueryCache × ℕ

/-- The indexed lazy table: the `j`-th fresh point is drawn from `sampler j`; repeated points are answered from the table. -/
noncomputable def indexedImpl (sampler : ℕ → ProbComp R) : QueryImpl (Spec D R) (StateT (IState D R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (IState D R) ProbComp) +
    (fun point => StateT.mk fun state => match state.1 point with
      | some answer => Pure.pure (answer, state)
      | none => do
          let answer ← sampler state.2
          Pure.pure (answer, (state.1.cacheQuery point answer, state.2 + 1)) :
      QueryImpl (D →ₒ R) (StateT (IState D R) ProbComp))

/-- The sampler family with the `k`-th fresh point answered by `value`. -/
def pin (k : ℕ) (value : R) (sampler : ℕ → ProbComp R) : ℕ → ProbComp R :=
  fun j => if j = k then Pure.pure value else sampler j

theorem pin_same (k : ℕ) (value : R) (sampler : ℕ → ProbComp R) : pin k value sampler k = Pure.pure value := by
  simp [pin]

theorem pin_other (k : ℕ) (value : R) (sampler : ℕ → ProbComp R) (j : ℕ) (other : j ≠ k) :
    pin k value sampler j = sampler j := by
  simp [pin, other]

/-- Pinning ignores the sampler at the pinned point. -/
theorem pin_congr (k : ℕ) (value : R) (sampler sampler' : ℕ → ProbComp R) (same : ∀ j, j ≠ k → sampler j = sampler' j) :
    pin k value sampler = pin k value sampler' := by
  funext j
  by_cases equal : j = k
  · simp [pin, equal]
  · simp [pin, equal, same j equal]

theorem indexed_coin (sampler : ℕ → ProbComp R) (coin : ℕ) (state : IState D R) :
    (indexedImpl sampler (.inl coin)).run state =
      (fun reply => (reply, state)) <$> (unifSpec.query coin : ProbComp _) := by
  simp [indexedImpl]

theorem indexed_hit (sampler : ℕ → ProbComp R) (point : D) (state : IState D R) (answer : R)
    (hit : state.1 point = some answer) :
    (indexedImpl sampler (.inr point)).run state = Pure.pure (answer, state) := by
  simp [indexedImpl, hit]

theorem indexed_miss (sampler : ℕ → ProbComp R) (point : D) (state : IState D R) (miss : state.1 point = none) :
    (indexedImpl sampler (.inr point)).run state = (do
      let answer ← sampler state.2
      Pure.pure (answer, (state.1.cacheQuery point answer, state.2 + 1))) := by
  simp [indexedImpl, miss]

/-- Eager sampling of the `k`-th fresh point: the indexed table has the output distribution of drawing the `k`-th fresh value first and answering the `k`-th fresh point with it. -/
theorem indexed_eager {α : Type} (sampler : ℕ → ProbComp R) (k : ℕ) (client : OracleComp (Spec D R) α)
    (state : IState D R) :
    EvalDistEq ((simulateQ (indexedImpl sampler) client).run state)
      (do let value ← sampler k; (simulateQ (indexedImpl (pin k value sampler)) client).run state) := by
  refine PqxdhServerAuthEntryFactor.eager_run (sampler k) (indexedImpl sampler)
    (fun value => indexedImpl (pin k value sampler)) (fun state => k < state.2) ?_ ?_ client state
  · intro query current done
    rcases query with coin | point
    · refine ⟨fun value => by rw [indexed_coin, indexed_coin], ?_⟩
      intro result member
      rw [indexed_coin, support_map] at member
      obtain ⟨reply, -, rfl⟩ := member
      exact done
    · rcases hit : current.1 point with _ | answer
      · refine ⟨fun value => by rw [indexed_miss _ _ _ hit, indexed_miss _ _ _ hit,
          pin_other _ _ _ _ (Nat.ne_of_gt done)], ?_⟩
        intro result member
        rw [indexed_miss _ _ _ hit, mem_support_bind_iff] at member
        obtain ⟨answer, -, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact Nat.lt_succ_of_lt done
      · refine ⟨fun value => by rw [indexed_hit _ _ _ _ hit, indexed_hit _ _ _ _ hit], ?_⟩
        intro result member
        rw [indexed_hit _ _ _ _ hit, support_pure, Set.mem_singleton_iff] at member
        subst member
        exact done
  · intro query current fresh
    rcases query with coin | point
    · exact Or.inl fun value => by rw [indexed_coin, indexed_coin]
    · rcases hit : current.1 point with _ | answer
      · by_cases at_k : current.2 = k
        · refine Or.inr ⟨?_, ?_⟩
          · simp only [indexed_miss _ _ _ hit, at_k, pin_same, pure_bind, EvalDistEq.refl]
          · intro value result member
            rw [indexed_miss _ _ _ hit, at_k, pin_same, pure_bind, support_pure, Set.mem_singleton_iff] at member
            subst member
            exact Nat.lt_succ_self k
        · exact Or.inl fun value => by rw [indexed_miss _ _ _ hit, indexed_miss _ _ _ hit, pin_other _ _ _ _ at_k]
      · exact Or.inl fun value => by rw [indexed_hit _ _ _ _ hit, indexed_hit _ _ _ _ hit]

/-- `indexed_eager` for the client's output, in the measure notation: the indexed table has the output distribution of drawing the `k`-th fresh value first and answering the `k`-th fresh point with it. -/
theorem indexed_eager_output {α : Type} [MeasurableSpace α] (sampler : ℕ → ProbComp R) (k : ℕ)
    (client : OracleComp (Spec D R) α) (state : IState D R) :
    𝒟[(simulateQ (indexedImpl sampler) client).run' state] =
      𝒟[do let value ← sampler k; (simulateQ (indexedImpl (pin k value sampler)) client).run' state] := by
  refine EvalDistEq.evalDist_eq ?_
  have project := (indexed_eager sampler k client state).map Prod.fst
  simpa [StateT.run'_eq, map_bind] using project

end Indexed

/-! ### The first-value table is the indexed table pinned at the first fresh point -/

section First

variable {D R : Type} [DecidableEq D]

/-- The common view of the first-value table and the pinned indexed table: whether a fresh point has been seen. -/
noncomputable def startedImpl (value : R) (sampler : ProbComp R) :
    QueryImpl (Spec D R) (StateT ((D →ₒ R).QueryCache × Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT ((D →ₒ R).QueryCache × Bool) ProbComp) +
    (fun point => StateT.mk fun state => match state.1 point with
      | some answer => Pure.pure (answer, state)
      | none => if state.2 then do
            let answer ← sampler
            Pure.pure (answer, (state.1.cacheQuery point answer, true))
          else Pure.pure (value, (state.1.cacheQuery point value, true)) :
      QueryImpl (D →ₒ R) (StateT ((D →ₒ R).QueryCache × Bool) ProbComp))

theorem firstTable_started {α : Type} (value : R) (sampler : ProbComp R) (client : OracleComp (Spec D R) α) :
    (simulateQ (PqxdhRegistrationJointKemEntryFactor.firstTable value sampler) client).run'
        ((∅ : (D →ₒ R).QueryCache), (none : Option D)) =
      (simulateQ (startedImpl value sampler) client).run' ((∅ : (D →ₒ R).QueryCache), false) := by
  refine OracleComp.run'_simulateQ_eq_of_query_map_eq (PqxdhRegistrationJointKemEntryFactor.firstTable value sampler)
    (startedImpl value sampler) (fun state => (state.1, state.2.isSome)) ?_ client
    ((∅ : (D →ₒ R).QueryCache), (none : Option D))
  intro query current
  obtain ⟨cache, first⟩ := current
  rcases query with coin | point
  · simp [PqxdhRegistrationJointKemEntryFactor.firstTable, startedImpl]
  · rcases hit : cache point with _ | answer
    · rcases first with _ | first
      · simp [PqxdhRegistrationJointKemEntryFactor.firstTable, startedImpl, hit]
      · simp [PqxdhRegistrationJointKemEntryFactor.firstTable, startedImpl, hit]
    · simp [PqxdhRegistrationJointKemEntryFactor.firstTable, startedImpl, hit]

theorem pinned_started {α : Type} (value : R) (sampler : ProbComp R) (client : OracleComp (Spec D R) α) :
    (simulateQ (indexedImpl (pin 0 value fun _ => sampler)) client).run' ((∅ : (D →ₒ R).QueryCache), 0) =
      (simulateQ (startedImpl value sampler) client).run' ((∅ : (D →ₒ R).QueryCache), false) := by
  refine OracleComp.run'_simulateQ_eq_of_query_map_eq (indexedImpl (pin 0 value fun _ => sampler))
    (startedImpl value sampler) (fun state => (state.1, decide (0 < state.2))) ?_ client
    ((∅ : (D →ₒ R).QueryCache), 0)
  intro query current
  obtain ⟨cache, fresh⟩ := current
  rcases query with coin | point
  · simp [indexedImpl, startedImpl]
  · rcases hit : cache point with _ | answer
    · rcases fresh with _ | fresh
      · simp [indexedImpl, startedImpl, hit, pin]
      · simp [indexedImpl, startedImpl, hit, pin]
    · simp [indexedImpl, startedImpl, hit]

/-- The first-value table of stage S3b is the indexed table pinned at its first fresh point. -/
theorem firstTable_pinned {α : Type} (value : R) (sampler : ProbComp R) (client : OracleComp (Spec D R) α) :
    (simulateQ (PqxdhRegistrationJointKemEntryFactor.firstTable value sampler) client).run'
        ((∅ : (D →ₒ R).QueryCache), (none : Option D)) =
      (simulateQ (indexedImpl (pin 0 value fun _ => sampler)) client).run' ((∅ : (D →ₒ R).QueryCache), 0) := by
  rw [firstTable_started, pinned_started]

end First

/-! ### Bounded clients see only the first samplers -/

section Bounded

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- A value request. -/
def IsValue {D R : Type} : (Spec D R).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance {D R : Type} : DecidablePred (IsValue (D := D) (R := R))
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

/-- VCVio's lazy uniform table on the points, beside uniform coins. -/
noncomputable def lazyImpl : QueryImpl (Spec D R) (StateT (D →ₒ R).QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (D →ₒ R).QueryCache ProbComp) + (D →ₒ R).randomOracle

/-- A client with at most `m` value requests, run from a table with `fresh` fresh points where `fresh + m ≤ q`, sees only the first `q` samplers; if these are uniform, the indexed table is the lazy uniform table. -/
theorem indexed_lazy {α : Type} (sampler : ℕ → ProbComp R) (q : ℕ) (uniform : ∀ j < q, sampler j = $ᵗ R)
    (client : OracleComp (Spec D R) α) (m : ℕ) (bounded : client.IsQueryBoundP (IsValue (D := D) (R := R)) m)
    (state : IState D R) (room : state.2 + m ≤ q) :
    Prod.map id Prod.fst <$> (simulateQ (indexedImpl sampler) client).run state =
      (simulateQ lazyImpl client).run state.1 := by
  induction client using OracleComp.inductionOn generalizing m state with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨cache, fresh⟩ := state
      simp only at room
      rcases query with coin | point
      · have rest : ∀ reply, (next reply).IsQueryBoundP (IsValue (D := D) (R := R)) m := fun reply => by
          simpa [IsValue] using bounded.2 reply
        have lazyCoin : (lazyImpl (D := D) (R := R) (.inl coin)).run cache =
            (fun reply => (reply, cache)) <$> (unifSpec.query coin : ProbComp _) := by
          simp [lazyImpl]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, indexed_coin, lazyCoin,
          bind_map_left]
        exact bind_congr fun reply => ih reply m (rest reply) (cache, fresh) room
      · have positive : 0 < m := by simpa [IsValue] using bounded.1
        have rest : ∀ reply, (next reply).IsQueryBoundP (IsValue (D := D) (R := R)) (m - 1) := fun reply => by
          simpa [IsValue] using bounded.2 reply
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
        rcases hit : cache point with _ | answer
        · have lazyMiss : (lazyImpl (D := D) (R := R) (.inr point)).run cache =
              (do let answer ← $ᵗ R; Pure.pure (answer, cache.cacheQuery point answer)) := by
            simp [lazyImpl, hit]
          rw [indexed_miss _ _ _ hit, lazyMiss, uniform fresh (by omega)]
          simp only [bind_assoc, pure_bind]
          refine bind_congr fun answer => ?_
          exact ih answer (m - 1) (rest answer) (cache.cacheQuery point answer, fresh + 1) (by simp only; omega)
        · have lazyHit : (lazyImpl (D := D) (R := R) (.inr point)).run cache = Pure.pure (answer, cache) := by
            simp [lazyImpl, hit]
          rw [indexed_hit _ _ _ _ hit, lazyHit, pure_bind, pure_bind]
          exact ih answer (m - 1) (rest answer) (cache, fresh) (by simp only; omega)

end Bounded

/-! ### The first-touch slot allocator -/

section Slots

variable {D R : Type} [DecidableEq D] [SampleableType R] {n : ℕ}

open PqxdhRecordLiftInterface (Slot)

/-- The allocator state: the slot of each point, and the next free slot. -/
abbrev Alloc (D : Type) (n : ℕ) := (D → Option (Slot n)) × ℕ

/-- The empty allocator. -/
def emptyAlloc : Alloc D n := (fun _ => none, 0)

/-- A slot service: how a handler obtains slot `j`'s value. -/
abbrev SlotService (S R : Type) (n : ℕ) := Slot n → StateT S ProbComp R

/-- The first-touch allocator in front of a slot service: a new point gets the next free slot, a repeated point keeps its slot, and the value is read only through the slot service. With no free slot left, a fresh point gets a fresh uniform value without a slot; `slot_lazy` shows that a client with at most `n` value requests never reaches that branch. -/
noncomputable def slotImpl {S : Type} (service : SlotService S R n) :
    QueryImpl (Spec D R) (StateT (Alloc D n × S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Alloc D n × S) ProbComp) +
    (fun point => StateT.mk fun state => match state.1.1 point with
      | some slot => (fun result => (result.1, (state.1, result.2))) <$> (service slot).run state.2
      | none => if room : state.1.2 < n then
            (fun result => (result.1, ((Function.update state.1.1 point (some ⟨state.1.2, room⟩), state.1.2 + 1),
              result.2))) <$> (service ⟨state.1.2, room⟩).run state.2
          else (fun answer => (answer, state)) <$> ($ᵗ R) :
      QueryImpl (D →ₒ R) (StateT (Alloc D n × S) ProbComp))

theorem slot_coin {S : Type} (service : SlotService S R n) (coin : ℕ) (state : Alloc D n × S) :
    (slotImpl service (.inl coin)).run state = (fun reply => (reply, state)) <$> (unifSpec.query coin : ProbComp _) := by
  simp [slotImpl]

theorem slot_some {S : Type} (service : SlotService S R n) (point : D) (state : Alloc D n × S) (slot : Slot n)
    (found : state.1.1 point = some slot) :
    (slotImpl service (.inr point)).run state =
      (fun result => (result.1, (state.1, result.2))) <$> (service slot).run state.2 := by
  simp [slotImpl, found]

theorem slot_none {S : Type} (service : SlotService S R n) (point : D) (state : Alloc D n × S)
    (found : state.1.1 point = none) (room : state.1.2 < n) :
    (slotImpl service (.inr point)).run state =
      (fun result => (result.1, ((Function.update state.1.1 point (some ⟨state.1.2, room⟩), state.1.2 + 1),
        result.2))) <$> (service ⟨state.1.2, room⟩).run state.2 := by
  simp [slotImpl, found, room]

/-- Naturality in exact form: a client of the allocator reads slot values only through the slot service, so a projection that carries each step of one slot service to the corresponding step of another by an exact program equality under an invariant (for example `LazyOracleDiscard.impl_project`) carries the whole run, with the allocator state unchanged. This is item 2's exact-form analogue of the property CE-11 calls `CoreNatural`, not that property, which takes service projections in law (`LawEq`) and concerns CE-11's per-command registration core. -/
theorem slot_natural {S₁ S₂ α : Type} (service₁ : SlotService S₁ R n) (service₂ : SlotService S₂ R n)
    (inv : S₁ → Prop) (proj : S₁ → S₂)
    (step : ∀ slot state, inv state →
      Prod.map id proj <$> (service₁ slot).run state = (service₂ slot).run (proj state))
    (keeps : ∀ slot state, inv state → ∀ result ∈ support ((service₁ slot).run state), inv result.2)
    (client : OracleComp (Spec D R) α) (alloc : Alloc D n) (state : S₁) (holds : inv state) :
    Prod.map id (Prod.map id proj) <$> (simulateQ (slotImpl service₁) client).run (alloc, state) =
      (simulateQ (slotImpl service₂) client).run (alloc, proj state) ∧
      ∀ result ∈ support ((simulateQ (slotImpl service₁) client).run (alloc, state)), inv result.2.2 := by
  refine PqxdhRegistrationJointKemEntryFactor.map_run_inv (slotImpl service₁) (slotImpl service₂)
    (fun current => inv current.2) (Prod.map id proj) ?_ ?_ client (alloc, state) holds
  · intro query current good result member
    rcases query with coin | point
    · rw [slot_coin, support_map] at member
      obtain ⟨reply, -, rfl⟩ := member
      exact good
    · rcases found : current.1.1 point with _ | slot
      · by_cases room : current.1.2 < n
        · rw [slot_none _ _ _ found room, support_map] at member
          obtain ⟨inner, innerMember, rfl⟩ := member
          exact keeps _ _ good inner innerMember
        · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, dite_false,
            support_map] at member
          obtain ⟨answer, -, rfl⟩ := member
          exact good
      · rw [slot_some _ _ _ _ found, support_map] at member
        obtain ⟨inner, innerMember, rfl⟩ := member
        exact keeps _ _ good inner innerMember
  · intro query current good
    obtain ⟨allocNow, inner⟩ := current
    simp only at good
    change Prod.map id (Prod.map id proj) <$> (slotImpl service₁ query).run (allocNow, inner) =
      (slotImpl service₂ query).run (allocNow, proj inner)
    rcases query with coin | point
    · rw [slot_coin, slot_coin, Functor.map_map]
      rfl
    · rcases found : allocNow.1 point with _ | slot
      · by_cases room : allocNow.2 < n
        · rw [slot_none (state := (allocNow, inner)) _ _ found room,
            slot_none (state := (allocNow, proj inner)) _ _ found room, ← step _ _ good, Functor.map_map,
            Functor.map_map]
          rfl
        · have left : (slotImpl service₁ (.inr point)).run (allocNow, inner) =
              (fun answer => (answer, (allocNow, inner))) <$> ($ᵗ R) := by
            simp [slotImpl, found, room]
          have right : (slotImpl service₂ (.inr point)).run (allocNow, proj inner) =
              (fun answer => (answer, (allocNow, proj inner))) <$> ($ᵗ R) := by
            simp [slotImpl, found, room]
          rw [left, right, Functor.map_map]
          rfl
      · rw [slot_some (state := (allocNow, inner)) _ _ _ found, slot_some (state := (allocNow, proj inner)) _ _ _ found,
          ← step _ _ good, Functor.map_map, Functor.map_map]
        rfl

/-- The persistent lazy table as a slot service. -/
noncomputable def tableService : SlotService (PqxdhRecordLiftLazyTable.State (Slot n →ₒ R)) R n :=
  fun slot => PqxdhRecordLiftLazyTable.impl slot

/-- The table on the points that the allocator and the slot table represent. -/
def cacheOf (state : Alloc D n × PqxdhRecordLiftLazyTable.State (Slot n →ₒ R)) : (D →ₒ R).QueryCache :=
  QueryCache.ofFn fun point => (state.1.1 point).bind fun slot => state.2.1 slot

/-- Allocated slots are below the next free slot and belong to one point each; free slots hold no value. -/
def SlotGood (state : Alloc D n × PqxdhRecordLiftLazyTable.State (Slot n →ₒ R)) : Prop :=
  (∀ point slot, state.1.1 point = some slot → slot.val < state.1.2) ∧
    (∀ point point' slot, state.1.1 point = some slot → state.1.1 point' = some slot → point = point') ∧
    ∀ slot : Slot n, state.1.2 ≤ slot.val → state.2.1 slot = none

omit [DecidableEq D] [SampleableType R] in
theorem slotGood_empty : SlotGood ((emptyAlloc : Alloc D n), (PqxdhRecordLiftLazyTable.initial :
    PqxdhRecordLiftLazyTable.State (Slot n →ₒ R))) := by
  refine ⟨fun _ _ found => ?_, fun _ _ _ found _ => ?_, fun _ _ => rfl⟩ <;> simp [emptyAlloc] at found

omit [DecidableEq D] [SampleableType R] in
theorem cacheOf_empty : cacheOf ((emptyAlloc : Alloc D n), (PqxdhRecordLiftLazyTable.initial :
    PqxdhRecordLiftLazyTable.State (Slot n →ₒ R))) = ∅ := rfl

/-- One value request of the allocator with the slot table, from a good state with a free slot left, is one step of the lazy table on the represented points, and keeps the state good, allocating at most one slot. -/
theorem slot_step (point : D) (state : Alloc D n × PqxdhRecordLiftLazyTable.State (Slot n →ₒ R))
    (good : SlotGood state) (room : state.1.2 < n) :
    Prod.map id cacheOf <$> (slotImpl tableService (.inr point)).run state =
        (lazyImpl (.inr point)).run (cacheOf state) ∧
      ∀ result ∈ support ((slotImpl tableService (.inr point)).run state),
        SlotGood result.2 ∧ result.2.1.2 ≤ state.1.2 + 1 := by
  obtain ⟨below, unique, free⟩ := good
  rcases found : state.1.1 point with _ | slot
  · have empty : state.2.1 ⟨state.1.2, room⟩ = none := free _ le_rfl
    have absent : cacheOf state point = none := by simp [cacheOf, found]
    have lazyMiss : (lazyImpl (D := D) (R := R) (.inr point)).run (cacheOf state) =
        (do let answer ← $ᵗ R; Pure.pure (answer, (cacheOf state).cacheQuery point answer)) := by
      simp [lazyImpl, absent]
    refine ⟨?_, ?_⟩
    · rw [slot_none _ _ _ found room, lazyMiss, tableService, PqxdhRecordLiftLazyTable.run_miss _ _ empty,
        Functor.map_map, Functor.map_map, map_eq_bind_pure_comp]
      refine bind_congr fun answer => ?_
      simp only [Function.comp_apply, Prod.map_apply, id_eq]
      congr 2
      apply QueryCache.ext
      intro other
      by_cases same : other = point
      · subst same
        simp [cacheOf]
      · simp only [cacheOf, QueryCache.ofFn_apply, Function.update_of_ne same, QueryCache.cacheQuery_of_ne _ _ same]
        rcases otherFound : state.1.1 other with _ | otherSlot
        · rfl
        · have distinct : otherSlot ≠ ⟨state.1.2, room⟩ := by
            intro equal
            have := below other otherSlot otherFound
            rw [equal] at this
            exact Nat.lt_irrefl _ this
          simp only [Option.bind_some, QueryCache.cacheQuery_of_ne _ _ distinct]
    · intro result member
      rw [slot_none _ _ _ found room, tableService, PqxdhRecordLiftLazyTable.run_miss _ _ empty, Functor.map_map,
        support_map] at member
      obtain ⟨answer, -, rfl⟩ := member
      refine ⟨⟨fun other otherSlot otherFound => ?_, fun first second sharedSlot firstFound secondFound => ?_,
        fun freeSlot after => ?_⟩, le_rfl⟩
      · by_cases same : other = point
        · subst same
          simp only [Function.update_self, Option.some.injEq] at otherFound
          subst otherFound
          exact Nat.lt_succ_self _
        · simp only [Function.update_of_ne same] at otherFound
          exact Nat.lt_succ_of_lt (below other otherSlot otherFound)
      · by_cases firstSame : first = point
        · by_cases secondSame : second = point
          · rw [firstSame, secondSame]
          · subst firstSame
            simp only [Function.update_self, Option.some.injEq] at firstFound
            simp only [Function.update_of_ne secondSame] at secondFound
            have := below second sharedSlot secondFound
            rw [← firstFound] at this
            exact absurd this (Nat.lt_irrefl _)
        · by_cases secondSame : second = point
          · subst secondSame
            simp only [Function.update_self, Option.some.injEq] at secondFound
            simp only [Function.update_of_ne firstSame] at firstFound
            have := below first sharedSlot firstFound
            rw [← secondFound] at this
            exact absurd this (Nat.lt_irrefl _)
          · simp only [Function.update_of_ne firstSame] at firstFound
            simp only [Function.update_of_ne secondSame] at secondFound
            exact unique first second sharedSlot firstFound secondFound
      · have distinct : freeSlot ≠ ⟨state.1.2, room⟩ := by
          intro equal
          rw [equal] at after
          exact Nat.not_succ_le_self _ after
        simp only [QueryCache.cacheQuery_of_ne _ _ distinct]
        exact free freeSlot (Nat.le_of_succ_le after)
  · have held : cacheOf state point = state.2.1 slot := by simp [cacheOf, found]
    rcases stored : state.2.1 slot with _ | answer
    · have lazyMiss : (lazyImpl (D := D) (R := R) (.inr point)).run (cacheOf state) =
          (do let answer ← $ᵗ R; Pure.pure (answer, (cacheOf state).cacheQuery point answer)) := by
        simp [lazyImpl, held, stored]
      refine ⟨?_, ?_⟩
      · rw [slot_some _ _ _ _ found, lazyMiss, tableService, PqxdhRecordLiftLazyTable.run_miss _ _ stored,
          Functor.map_map, Functor.map_map, map_eq_bind_pure_comp]
        refine bind_congr fun answer => ?_
        simp only [Function.comp_apply, Prod.map_apply, id_eq]
        congr 2
        apply QueryCache.ext
        intro other
        by_cases same : other = point
        · subst same
          simp [cacheOf, found]
        · simp only [cacheOf, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ same]
          rcases otherFound : state.1.1 other with _ | otherSlot
          · rfl
          · have distinct : otherSlot ≠ slot := by
              intro equal
              rw [equal] at otherFound
              exact same (unique other point slot otherFound found)
            simp only [Option.bind_some, QueryCache.cacheQuery_of_ne _ _ distinct]
      · intro result member
        rw [slot_some _ _ _ _ found, tableService, PqxdhRecordLiftLazyTable.run_miss _ _ stored, Functor.map_map,
          support_map] at member
        obtain ⟨answer, -, rfl⟩ := member
        refine ⟨⟨below, unique, fun freeSlot after => ?_⟩, Nat.le_succ _⟩
        have distinct : freeSlot ≠ slot := by
          intro equal
          rw [equal] at after
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (below point slot found) after)
        simp only [QueryCache.cacheQuery_of_ne _ _ distinct]
        exact free freeSlot after
    · have lazyHit : (lazyImpl (D := D) (R := R) (.inr point)).run (cacheOf state) =
          Pure.pure (answer, cacheOf state) := by
        simp [lazyImpl, held, stored]
      refine ⟨?_, ?_⟩
      · rw [slot_some _ _ _ _ found, lazyHit, tableService, PqxdhRecordLiftLazyTable.run_hit _ _ _ stored, map_pure,
          map_pure]
        rfl
      · intro result member
        rw [slot_some _ _ _ _ found, tableService, PqxdhRecordLiftLazyTable.run_hit _ _ _ stored, map_pure,
          support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨⟨below, unique, free⟩, Nat.le_succ _⟩

/-- A client with at most `m` value requests, from a good state with at least `m` free slots, run through the allocator and the persistent slot table, is the lazy uniform table on the points: with at most `n` value requests no point is left without a slot. -/
theorem slot_lazy {α : Type} (client : OracleComp (Spec D R) α) (m : ℕ)
    (bounded : client.IsQueryBoundP (IsValue (D := D) (R := R)) m)
    (state : Alloc D n × PqxdhRecordLiftLazyTable.State (Slot n →ₒ R)) (good : SlotGood state)
    (room : state.1.2 + m ≤ n) :
    Prod.map id cacheOf <$> (simulateQ (slotImpl tableService) client).run state =
      (simulateQ lazyImpl client).run (cacheOf state) := by
  induction client using OracleComp.inductionOn generalizing m state with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rcases query with coin | point
      · have rest : ∀ reply, (next reply).IsQueryBoundP (IsValue (D := D) (R := R)) m := fun reply => by
          simpa [IsValue] using bounded.2 reply
        have lazyCoin : (lazyImpl (D := D) (R := R) (.inl coin)).run (cacheOf state) =
            (fun reply => (reply, cacheOf state)) <$> (unifSpec.query coin : ProbComp _) := by
          simp [lazyImpl]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, slot_coin, lazyCoin,
          bind_map_left]
        exact bind_congr fun reply => ih reply m (rest reply) state good room
      · have positive : 0 < m := by simpa [IsValue] using bounded.1
        have rest : ∀ reply, (next reply).IsQueryBoundP (IsValue (D := D) (R := R)) (m - 1) := fun reply => by
          simpa [IsValue] using bounded.2 reply
        obtain ⟨same, supported⟩ := slot_step point state good (by omega)
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
        rw [← same, bind_map_left]
        refine bind_congr_of_forall_mem_support _ fun result member => ?_
        obtain ⟨resultGood, grown⟩ := supported result member
        exact ih result.1 (m - 1) (rest result.1) result.2 resultGood (by omega)

end Slots

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pin_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pin_same

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pin_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pin_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pin_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pin_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_coin' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_hit' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_miss' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_eager

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_eager_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_eager_output

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.firstTable_started' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.firstTable_started

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pinned_started' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.pinned_started

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.firstTable_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.firstTable_pinned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_lazy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.indexed_lazy

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_some

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_none

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_natural

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slotGood_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slotGood_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.cacheOf_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.cacheOf_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_lazy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slot_lazy
