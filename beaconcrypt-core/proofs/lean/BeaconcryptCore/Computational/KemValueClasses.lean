import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Data.List.Nodup

/-!
A private finite value-class table represents actual primitive replies without assuming key, coin, ciphertext or secret injectivity. Interning compares the actual values and either reuses an existing representative or appends a new one. The existing/fresh transition permits both ordinary distinct outputs and actual aliases. Equal classes correspond to equal values only in the same retained table; independently assigning a new class in two different tables supplies no such implication.

The annotated interpreter returns the original dependent reply and retains the complete original primitive state, including optional rejection and state-dependent effects. An arbitrary adaptive client therefore takes exactly the same equality/disequality branches and makes exactly the same underlying oracle requests. A separate branch theorem supports replacing a comparison only after its two retained lookup relations have been established. Optional encapsulation-shaped replies retain the original ciphertext/shared-secret pair; no generated key, recovered plaintext or assumed secret value is supplied to the client.

Classes and representative values are private ghost state. Their numerical indices are not public wire encodings, guess-resistant names, keys or new adversary endpoints, and the table is excluded from every reveal, snapshot and persistence interface. These statements describe an instrumented mathematical experiment, not a native implementation or physical-erasure claim. Unique representatives follow from actual insertion, with at most one new class per field and two per optional pair. Exact oracle-cap equivalence does not make value comparisons, byte processing or table scans free; the table is analysis-only local work.

This normalization does not impose an input-independent shared secret or transfer protocol results from the fixed public-key quotient. It does not prove a ProVerif process simulation, probability bound for fresh hidden-value collisions, ordinary ML-KEM IND-CCA reduction, source primitive implementation, or global secrecy/authentication. Those connections must retain actual public evaluations, complete input consistency, fresh coin distributions, challenge blocking, all replies, source/reduction query accounting and the existing reveal/compromise policies.
-/

open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.KemValueClasses

/-- Intern an actual value in first-occurrence order, reusing an existing representative or appending one. -/
def intern {Value : Type} [DecidableEq Value] (value : Value) :
    List Value → Nat × List Value
  | [] => (0, [value])
  | head :: tail =>
    if head = value then (0, head :: tail)
    else
      let result := intern value tail
      (result.1 + 1, head :: result.2)

/-- The returned class always resolves to the actual supplied value. -/
theorem intern_value {Value : Type} [DecidableEq Value] (value : Value)
    (values : List Value) :
    (intern value values).2[(intern value values).1]? = some value := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    by_cases h : head = value <;> simp_all [intern]

/-- Interning never changes or removes an existing table entry. -/
theorem intern_extends {Value : Type} [DecidableEq Value] (value : Value)
    (values : List Value) :
    ∃ suffix, (intern value values).2 = values ++ suffix := by
  induction values with
  | nil => exact ⟨[value], rfl⟩
  | cons head tail ih =>
    by_cases h : head = value
    · exact ⟨[], by simp [intern, h]⟩
    · obtain ⟨suffix, hs⟩ := ih
      exact ⟨suffix, by simp [intern, h, hs]⟩

/-- The only possible new represented value is the actual supplied value. -/
theorem mem_intern {Value : Type} [DecidableEq Value] (value found : Value)
    (values : List Value) :
    found ∈ (intern value values).2 ↔ found = value ∨ found ∈ values := by
  induction values with
  | nil => simp [intern]
  | cons head tail ih =>
    by_cases h : head = value
    · simp [intern, h]
    · simp only [intern, h, ↓reduceIte, List.mem_cons, ih]
      tauto

/-- An actual repeated value leaves the entire table unchanged. -/
theorem intern_existing {Value : Type} [DecidableEq Value] (value : Value)
    (values : List Value) (present : value ∈ values) :
    (intern value values).2 = values := by
  induction values with
  | nil => simp at present
  | cons head tail ih =>
    by_cases same : head = value
    · simp [intern, same]
    · have tailPresent : value ∈ tail := by simpa [Ne.symm same] using present
      simp [intern, same, ih tailPresent]

/-- An actually absent value appends exactly one representative at the old length. -/
theorem intern_fresh {Value : Type} [DecidableEq Value] (value : Value)
    (values : List Value) (fresh : value ∉ values) :
    intern value values = (values.length, values ++ [value]) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    have different : head ≠ value := fun h => fresh (by simp [h])
    have absent : value ∉ tail := fun h => fresh (by simp [h])
    simp [intern, different, ih absent]

/-- Every actual reply has an existing-class or new-class transition; neither branch is forced by its primitive inputs. -/
theorem intern_transition {Value : Type} [DecidableEq Value] (value : Value)
    (values : List Value) :
    ((intern value values).1 < values.length ∧ (intern value values).2 = values) ∨
      intern value values = (values.length, values ++ [value]) := by
  by_cases present : value ∈ values
  · have unchanged := intern_existing value values present
    have lookup := intern_value value values
    rw [unchanged] at lookup
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp lookup
    exact Or.inl ⟨bound, unchanged⟩
  · exact Or.inr (intern_fresh value values present)

/-- Unique representatives remain unique after interning any actual value. -/
theorem intern_nodup {Value : Type} [DecidableEq Value] (value : Value)
    (values : List Value) (unique : values.Nodup) :
    (intern value values).2.Nodup := by
  induction values with
  | nil => simp [intern]
  | cons head tail ih =>
    by_cases h : head = value
    · simpa [intern, h] using unique
    · have parts := List.nodup_cons.mp unique
      simp only [intern, h, ↓reduceIte, List.nodup_cons]
      exact ⟨by simpa [mem_intern, h] using parts.1, ih parts.2⟩

/-- Every previously assigned class retains its exact value. -/
theorem intern_preserves_lookup {Value : Type} [DecidableEq Value]
    (value found : Value) (values : List Value) (index : Nat)
    (present : values[index]? = some found) :
    (intern value values).2[index]? = some found := by
  obtain ⟨suffix, hs⟩ := intern_extends value values
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp present
  rw [hs, List.getElem?_append_left hlt]
  exact present

/-- One value adds at most one class. -/
theorem intern_length {Value : Type} [DecidableEq Value]
    (value : Value) (values : List Value) :
    (intern value values).2.length ≤ values.length + 1 := by
  induction values with
  | nil => simp [intern]
  | cons head tail ih =>
    by_cases h : head = value
    · simp [intern, h]
    · simpa only [intern, h, ↓reduceIte, List.length_cons] using Nat.add_le_add_right ih 1

/-- Record a finite list of actual input/reply fields in their supplied order. -/
def record {Value : Type} [DecidableEq Value] : List Value → List Value → List Value
  | [], values => values
  | next :: rest, values => record rest (intern next values).2

/-- A complete field list preserves representative uniqueness. -/
theorem record_nodup {Value : Type} [DecidableEq Value]
    (observed values : List Value) (unique : values.Nodup) :
    (record observed values).Nodup := by
  induction observed generalizing values with
  | nil => exact unique
  | cons next rest ih => exact ih _ (intern_nodup next values unique)

/-- Later finite histories preserve every earlier class/value association. -/
theorem record_preserves_lookup {Value : Type} [DecidableEq Value]
    (observed values : List Value) (found : Value) (index : Nat)
    (present : values[index]? = some found) :
    (record observed values)[index]? = some found := by
  induction observed generalizing values with
  | nil => exact present
  | cons next rest ih =>
    exact ih _ (intern_preserves_lookup next found values index present)

/-- A field list adds no more classes than its actual length. -/
theorem record_length {Value : Type} [DecidableEq Value]
    (observed values : List Value) :
    (record observed values).length ≤ values.length + observed.length := by
  induction observed generalizing values with
  | nil => simp [record]
  | cons next rest ih =>
    have first := intern_length next values
    have remaining := ih (intern next values).2
    simp only [record, List.length_cons]
    omega

/-- Two retained classes are equal exactly when their actual values are equal in the same unique table. -/
theorem classes_eq_iff {Value : Type} (values : List Value) (unique : values.Nodup)
    (left right : Value) (leftClass rightClass : Nat)
    (hleft : values[leftClass]? = some left)
    (hright : values[rightClass]? = some right) :
    leftClass = rightClass ↔ left = right := by
  constructor
  · intro same
    rw [same, hright] at hleft
    exact Option.some.inj hleft.symm
  · intro same
    obtain ⟨hl, vl⟩ := List.getElem?_eq_some_iff.mp hleft
    obtain ⟨hr, vr⟩ := List.getElem?_eq_some_iff.mp hright
    exact unique.getElem_inj_iff.mp (vl.trans (same.trans vr.symm))

/-- Sequential insertion preserves value equality, including aliases across different primitive inputs. -/
theorem sequential_classes_eq_iff {Value : Type} [DecidableEq Value]
    (left right : Value) (values : List Value) (unique : values.Nodup) :
    (intern left values).1 = (intern right (intern left values).2).1 ↔ left = right := by
  exact classes_eq_iff (intern right (intern left values).2).2
    (intern_nodup right _ (intern_nodup left _ unique)) left right _ _
    (intern_preserves_lookup right left _ _ (intern_value left values))
    (intern_value right (intern left values).2)

/-- Equality and disequality choose exactly the same continuation result under the retained representation. -/
theorem branch_eq {Value Result : Type} [DecidableEq Value]
    (values : List Value) (unique : values.Nodup) (left right : Value)
    (leftClass rightClass : Nat) (hleft : values[leftClass]? = some left)
    (hright : values[rightClass]? = some right) (equalCase differentCase : Result) :
    (if leftClass = rightClass then equalCase else differentCase) =
      (if left = right then equalCase else differentCase) := by
  simp only [classes_eq_iff values unique left right leftClass rightClass hleft hright]

/-- Run the unchanged interpreter first, then retain selected actual fields only in private ghost state. -/
def annotatedImpl {Value State : Type} [DecidableEq Value]
    {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl spec (StateT State m))
    (observed : (query : spec.Domain) → spec.Range query → List Value) :
    QueryImpl spec (StateT (State × List Value) m) := fun query state => do
  let result ← impl query state.1
  pure (result.1, (result.2, record (observed query result.1) state.2))

/-- Erasing only the ghost table retains the actual dependent reply and complete primitive poststate. -/
theorem annotated_step {Value State : Type} [DecidableEq Value]
    {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec (StateT State m))
    (observed : (query : spec.Domain) → spec.Range query → List Value)
    (query : spec.Domain) (state : State) (classes : List Value) :
    (fun result => (result.1, result.2.1)) <$>
      annotatedImpl impl observed query (state, classes) = impl query state := by
  simp [annotatedImpl]

/-- Every adaptive continuation receives its actual reply; erasure is equality of complete interpreted programs. -/
theorem annotated_execution {Value State Result : Type} [DecidableEq Value]
    {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec (StateT State m))
    (observed : (query : spec.Domain) → spec.Range query → List Value)
    (client : OracleComp spec Result) (state : State) (classes : List Value) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (annotatedImpl impl observed) client).run (state, classes) =
        (simulateQ impl client).run state := by
  induction client using OracleComp.inductionOn generalizing state classes with
  | pure result => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [map_bind, ih]
    simp [StateT.run, annotatedImpl]

/-- Every selective underlying-oracle cap is exactly the original cap, including all rejected replies. -/
theorem annotated_query_bounds {Value State Result : Type} [DecidableEq Value]
    {ι κ : Type} {spec : OracleSpec ι} {base : OracleSpec κ}
    (impl : QueryImpl spec (StateT State (OracleComp base)))
    (observed : (query : spec.Domain) → spec.Range query → List Value)
    (client : OracleComp spec Result) (state : State) (classes : List Value)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((simulateQ (annotatedImpl impl observed) client).run (state, classes)).IsQueryBoundP predicate bound ↔
      ((simulateQ impl client).run state).IsQueryBoundP predicate bound := by
  rw [← annotated_execution impl observed client state classes]
  exact (OracleComp.isQueryBoundP_map_iff _ _ _).symm

/-- Every supported complete run preserves unique representatives, starting from any unique table. -/
theorem annotated_supported_nodup {Value State Result : Type} [DecidableEq Value]
    {ι κ : Type} {spec : OracleSpec ι} {base : OracleSpec κ}
    (impl : QueryImpl spec (StateT State (OracleComp base)))
    (observed : (query : spec.Domain) → spec.Range query → List Value)
    (client : OracleComp spec Result) (state : State) (classes : List Value)
    (unique : classes.Nodup) (result : Result × (State × List Value))
    (present : result ∈ support ((simulateQ (annotatedImpl impl observed) client).run (state, classes))) :
    result.2.2.Nodup := by
  induction client using OracleComp.inductionOn generalizing state classes result with
  | pure value =>
    simpa using present ▸ unique
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at present
    simp only [StateT.run, annotatedImpl, bind_assoc, pure_bind, mem_support_bind_iff] at present
    obtain ⟨reply, _, remaining⟩ := present
    exact ih reply.1 reply.2 _ (record_nodup _ _ unique) result remaining

/-- Optional encapsulation replies record their actual ciphertext and shared-secret values; rejection records no value. -/
def optionalPairValues {Value : Type} : Option (Value × Value) → List Value
  | none => []
  | some pair => [pair.1, pair.2]

/-- Both optional outcomes retain the actual primitive poststate, and success records the two original values sequentially. -/
theorem optional_pair_run {Input Value State : Type} [DecidableEq Value]
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (Input →ₒ Option (Value × Value)) (StateT State m))
    (input : Input) (state : State) (classes : List Value) :
    annotatedImpl impl (fun _ => optionalPairValues) input (state, classes) =
      (do let result ← impl input state
          match result.1 with
          | none => pure (none, (result.2, classes))
          | some pair => pure (some pair,
              (result.2, (intern pair.2 (intern pair.1 classes).2).2))) := by
  unfold annotatedImpl
  congr 1
  funext result
  rcases result with ⟨reply, after⟩
  cases reply <;> rfl

/-- One optional pair adds at most two ghost classes, including rejection and equal-value cases. -/
theorem optional_pair_length {Value : Type} [DecidableEq Value]
    (reply : Option (Value × Value)) (classes : List Value) :
    (record (optionalPairValues reply) classes).length ≤ classes.length + 2 := by
  have bounded := record_length (optionalPairValues reply) classes
  cases reply with
  | none => simp [optionalPairValues, record]
  | some pair => simpa [optionalPairValues] using bounded

end BeaconcryptCore.Computational.KemValueClasses

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_value

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_extends' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_extends

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.mem_intern' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.mem_intern

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_existing' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_existing

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_fresh' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_fresh

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_transition

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_nodup

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_preserves_lookup' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_preserves_lookup

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.intern_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.intern_length

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.record_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.record_nodup

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.record_preserves_lookup' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.record_preserves_lookup

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.record_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.record_length

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.classes_eq_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.classes_eq_iff

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.sequential_classes_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.sequential_classes_eq_iff

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.branch_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.branch_eq

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.annotated_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.annotated_step

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.annotated_execution' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.annotated_execution

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.annotated_query_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.annotated_query_bounds

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.annotated_supported_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.annotated_supported_nodup

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.optional_pair_run' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.optional_pair_run

/--
info: 'BeaconcryptCore.Computational.KemValueClasses.optional_pair_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.KemValueClasses.optional_pair_length
