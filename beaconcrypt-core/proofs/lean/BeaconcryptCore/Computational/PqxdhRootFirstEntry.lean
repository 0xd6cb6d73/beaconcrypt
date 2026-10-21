import BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid
import BeaconcryptCore.Computational.PqxdhServerAuthEntrySimulation

/-!
# Eager sampling of the first fresh entry of a lazy uniform table (item 2, stage S3a)

This module is generic and contains no protocol code. A lazily sampled uniform table answers each fresh point with a fresh uniform value and repeats the stored value at a repeated point. The main theorem `eager_first` says that the first fresh entry may be sampled before the run starts: the lazy table, tracked with the point of its first fresh entry, has the same output distribution as the run that first draws `value` uniformly and then answers the first fresh point with `value`, every later fresh point with a fresh uniform value, and every repeated point from the table. No value is programmed: this is a distribution equality, proved with the generic eager-sampling lemma `PqxdhServerAuthEntryFactor.eager_run`.

The tracked lazy table records the point of its first fresh entry and is otherwise the lazy table: `tracked_project` shows that forgetting that point gives exactly the run of `lazyImpl`, VCVio's lazy random oracle beside uniform coins. `first_cached` shows that in the eager run the recorded first point always holds `value`, so later stages can identify entry 0 by its recorded point and read its root as `value`.

The item 2 plan applies this to the root table of `PqxdhCorrelatedExpandHybrid.uniformGame` (`uniformImpl_eq`, `uniformGame_first`): in that game every root request is a hidden table entry and the table starts empty, so entry 0 is the first root request in execution order and its uniform root is drawn first.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRootFirstEntry

section Generic

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- The table state with the point of its first fresh entry, once there is one. -/
abbrev State (D R : Type) := (D →ₒ R).QueryCache × Option D

/-- The lazy uniform table beside uniform coins (VCVio's lazy random oracle). -/
noncomputable def lazyImpl : QueryImpl (unifSpec + (D →ₒ R)) (StateT (D →ₒ R).QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (D →ₒ R).QueryCache ProbComp) +
    (D →ₒ R).randomOracle

/-- The lazy table that also records the point of its first fresh entry. -/
noncomputable def trackedTable : QueryImpl (D →ₒ R) (StateT (State D R) ProbComp) :=
  fun point => StateT.mk fun state => match state.1 point with
    | some answer => pure (answer, state)
    | none => do
        let answer ← $ᵗ R
        pure (answer, (state.1.cacheQuery point answer, some (state.2.getD point)))

/-- The tracked lazy table beside uniform coins. -/
noncomputable def trackedImpl : QueryImpl (unifSpec + (D →ₒ R)) (StateT (State D R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State D R) ProbComp) + trackedTable (D := D) (R := R)

/-- The eager table: the first fresh point receives the pre-drawn `value`; later fresh points receive fresh uniform values; repeated points are answered from the table. -/
noncomputable def eagerTable (value : R) : QueryImpl (D →ₒ R) (StateT (State D R) ProbComp) :=
  fun point => StateT.mk fun state => match state.1 point with
    | some answer => pure (answer, state)
    | none => match state.2 with
      | none => pure (value, (state.1.cacheQuery point value, some point))
      | some first => do
          let answer ← $ᵗ R
          pure (answer, (state.1.cacheQuery point answer, some first))

/-- The eager table beside uniform coins. -/
noncomputable def eagerImpl (value : R) : QueryImpl (unifSpec + (D →ₒ R)) (StateT (State D R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State D R) ProbComp) + eagerTable (D := D) value

/-- A repeated point of the tracked table is answered from the table and changes nothing. -/
theorem tracked_hit (point : D) (state : State D R) (answer : R) (hit : state.1 point = some answer) :
    (trackedImpl (.inr point)).run state = pure (answer, state) := by
  simp [trackedImpl, trackedTable, hit]

/-- A fresh point of the tracked table receives a fresh uniform value and is recorded as the first entry if there was none. -/
theorem tracked_miss (point : D) (state : State D R) (miss : state.1 point = none) :
    (trackedImpl (.inr point)).run state = (do
      let answer ← $ᵗ R
      pure (answer, (state.1.cacheQuery point answer, some (state.2.getD point)))) := by
  simp [trackedImpl, trackedTable, miss]

/-- A repeated point of the eager table is answered from the table and changes nothing. -/
theorem eager_hit (value : R) (point : D) (state : State D R) (answer : R)
    (hit : state.1 point = some answer) :
    (eagerImpl value (.inr point)).run state = pure (answer, state) := by
  simp [eagerImpl, eagerTable, hit]

/-- The first fresh point of the eager table receives the pre-drawn value and becomes the first entry. -/
theorem eager_first_miss (value : R) (point : D) (cache : (D →ₒ R).QueryCache)
    (miss : cache point = none) :
    (eagerImpl value (.inr point)).run (cache, none) =
      pure (value, (cache.cacheQuery point value, some point)) := by
  simp [eagerImpl, eagerTable, miss]

/-- A later fresh point of the eager table receives a fresh uniform value; the first entry is unchanged. -/
theorem eager_later_miss (value : R) (point first : D) (cache : (D →ₒ R).QueryCache)
    (miss : cache point = none) :
    (eagerImpl value (.inr point)).run (cache, some first) = (do
      let answer ← $ᵗ R
      pure (answer, (cache.cacheQuery point answer, some first))) := by
  simp [eagerImpl, eagerTable, miss]

/-- Forgetting the recorded first point turns every tracked run into the run of the lazy table. -/
theorem tracked_project {α : Type} (client : OracleComp (unifSpec + (D →ₒ R)) α) (state : State D R) :
    Prod.map id Prod.fst <$> (simulateQ trackedImpl client).run state =
      (simulateQ lazyImpl client).run state.1 := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq trackedImpl lazyImpl Prod.fst ?_ client state
  intro query current
  rcases query with coin | point
  · simp [trackedImpl, lazyImpl]
  · cases hit : current.1 point with
    | none =>
        simp [trackedImpl, trackedTable, lazyImpl, hit]
    | some answer =>
        simp [trackedImpl, trackedTable, lazyImpl, hit]

/-- Once a first entry is recorded, the eager and tracked tables take the same step, and the tracked step keeps a first entry recorded. -/
theorem eager_done (query : (unifSpec + (D →ₒ R)).Domain) (state : State D R)
    (done : state.2.isSome) :
    (∀ value, (eagerImpl value query).run state = (trackedImpl query).run state) ∧
      ∀ result ∈ support ((trackedImpl query).run state), result.2.2.isSome := by
  obtain ⟨cache, first⟩ := state
  obtain ⟨first, rfl⟩ := Option.isSome_iff_exists.mp done
  rcases query with coin | point
  · refine ⟨fun value => by simp [eagerImpl, trackedImpl], ?_⟩
    intro result member
    simp [trackedImpl] at member
    obtain ⟨_, rfl⟩ := member
    rfl
  · cases hit : cache point with
    | none =>
        refine ⟨fun value => by simp [eagerImpl, eagerTable, trackedImpl, trackedTable, hit], ?_⟩
        intro result member
        simp [trackedImpl, trackedTable, hit] at member
        obtain ⟨_, rfl⟩ := member
        rfl
    | some answer =>
        refine ⟨fun value => by simp [eagerImpl, eagerTable, trackedImpl, trackedTable, hit], ?_⟩
        intro result member
        simp [trackedImpl, trackedTable, hit] at member
        subst member
        rfl

/-- Before a first entry is recorded, a step either does not use the eager value, or it is the first fresh point: then the tracked step is the eager step on a uniform value drawn just before it, and it records a first entry. -/
theorem eager_fresh (query : (unifSpec + (D →ₒ R)).Domain) (state : State D R)
    (fresh : ¬ state.2.isSome) :
    (∀ value, (eagerImpl value query).run state = (trackedImpl query).run state) ∨
      ((trackedImpl query).run state = (do let value ← $ᵗ R; (eagerImpl value query).run state) ∧
        ∀ value, ∀ result ∈ support ((eagerImpl value query).run state), result.2.2.isSome) := by
  obtain ⟨cache, first⟩ := state
  have none : first = none := by simpa using fresh
  subst none
  rcases query with coin | point
  · exact Or.inl fun value => by simp [eagerImpl, trackedImpl]
  · cases hit : cache point with
    | some answer =>
        exact Or.inl fun value => by simp [eagerImpl, eagerTable, trackedImpl, trackedTable, hit]
    | none =>
        refine Or.inr ⟨?_, ?_⟩
        · simp [eagerImpl, eagerTable, trackedImpl, trackedTable, hit]
        · intro value result member
          simp [eagerImpl, eagerTable, hit] at member
          subst member
          rfl

/-- Eager sampling of the first fresh entry: the tracked lazy table has the output distribution of drawing the first fresh entry's value first and running the eager table. -/
theorem eager_first {α : Type} (client : OracleComp (unifSpec + (D →ₒ R)) α) (state : State D R) :
    EvalDistEq ((simulateQ trackedImpl client).run state)
      (do let value ← $ᵗ R; (simulateQ (eagerImpl value) client).run state) :=
  PqxdhServerAuthEntryFactor.eager_run ($ᵗ R) trackedImpl eagerImpl (fun state => state.2.isSome)
    eager_done (fun query state fresh => (eager_fresh query state fresh).imp id
      fun ⟨same, done⟩ => ⟨by rw [same], done⟩) client state

/-- Eager sampling of the first fresh entry, for the lazy table itself: from a state with no recorded first entry, the lazy table has the output distribution of the eager run with the first point forgotten. -/
theorem lazy_first {α : Type} (client : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) :
    EvalDistEq ((simulateQ lazyImpl client).run cache)
      (do let value ← $ᵗ R
          Prod.map id Prod.fst <$> (simulateQ (eagerImpl value) client).run (cache, none)) := by
  rw [← tracked_project client (cache, none)]
  refine ((eager_first client (cache, none)).map (Prod.map id Prod.fst)).trans ?_
  rw [map_bind]

/-- In the eager run, the recorded first point holds the pre-drawn value. -/
theorem first_cached {α : Type} (value : R) (client : OracleComp (unifSpec + (D →ₒ R)) α)
    (state : State D R) (start : ∀ first, state.2 = some first → state.1 first = some value) :
    ∀ result ∈ support ((simulateQ (eagerImpl value) client).run state),
      ∀ first, result.2.2 = some first → result.2.1 first = some value := by
  refine OracleComp.simulateQ_run_preserves_inv_of_query (eagerImpl value)
    (fun state : State D R => ∀ first, state.2 = some first → state.1 first = some value) ?_ client state start
  intro query current holds result member
  obtain ⟨cache, recorded⟩ := current
  rcases query with coin | point
  · simp [eagerImpl] at member
    obtain ⟨_, rfl⟩ := member
    exact holds
  · cases hit : cache point with
    | some answer =>
        simp [eagerImpl, eagerTable, hit] at member
        subst member
        exact holds
    | none =>
        cases recorded with
        | none =>
            simp [eagerImpl, eagerTable, hit] at member
            subst member
            intro first same
            cases same
            simp
        | some recordedFirst =>
            simp [eagerImpl, eagerTable, hit] at member
            obtain ⟨answer, rfl⟩ := member
            intro first same
            have equal : recordedFirst = first := by simpa using same
            subst equal
            have old := holds recordedFirst rfl
            have distinct : recordedFirst ≠ point := by
              intro equal
              subst equal
              simp [hit] at old
            simpa [QueryCache.cacheQuery_of_ne _ _ distinct] using old

end Generic

/-! ### The root table of the root Expand hybrid -/

open PqxdhSecretInputKdf PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpand

/-- The uniform-root handler of `PqxdhCorrelatedExpandHybrid` is the lazy table of 32-byte roots keyed by 128-byte coordinates. -/
theorem uniformImpl_eq :
    PqxdhCorrelatedExpandHybrid.uniformImpl = (lazyImpl : QueryImpl (unifSpec + (Message →ₒ RootOutput)) _) :=
  rfl

/-- The uniform-root game with the first root drawn first: entry 0's root is a uniform 32-byte value drawn before the client runs, and the first fresh root request is answered with it. -/
theorem uniformGame_first (client : OracleComp RootSpec Bool) :
    𝒟[PqxdhCorrelatedExpandHybrid.uniformGame client] =
      𝒟[do let root ← $ᵗ RootOutput
           (simulateQ (eagerImpl root) client).run' (∅, none)] := by
  refine EvalDistEq.evalDist_eq ?_
  have project := (lazy_first (D := Message) (R := RootOutput) client ∅).map Prod.fst
  simpa [PqxdhCorrelatedExpandHybrid.uniformGame, uniformImpl_eq, StateT.run'_eq, map_bind,
    Functor.map_map, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ] using project

end BeaconcryptCore.Computational.PqxdhRootFirstEntry

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.tracked_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.tracked_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.tracked_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.tracked_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_first_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_first_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_later_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_later_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.tracked_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.tracked_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_done

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.eager_first

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.lazy_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.lazy_first

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.first_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.first_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.uniformImpl_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.uniformImpl_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRootFirstEntry.uniformGame_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootFirstEntry.uniformGame_first
