-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame

/-! One actual persistent G2 uniform108-byte table splits exactly into selected and nonselected tables by a fixed private full-input predicate. This is an adaptive cache projection, not an independence assumption on an earlier PRK context. The selected table can subsequently be relabelled by first touch and split into material44/private64; nonselected outputs remain locally owned known kernels. Literal byte aliases remain aliases within their unique side. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3Partition
open PqxdhServerAuthKeySchedule (Output)
open RegistrationNativeG3FirstTouch (Spec)
variable {Value : Type}
attribute [local irreducible] uniformSample

abbrev Cache := (Pqxdh.Bytes →ₒ Output).QueryCache
abbrev State := Cache × Cache

def join (selected : Pqxdh.Bytes → Bool) (before : State) : Cache :=
  ⟨fun point => if selected point then before.1 point else before.2 point⟩

noncomputable def handler (selected : Pqxdh.Bytes → Bool) : QueryImpl Spec (StateT State ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr point => fun before => if selected point then
      (fun result => (result.1, (result.2, before.2))) <$> ((Pqxdh.Bytes →ₒ Output).randomOracle point).run before.1
    else (fun result => (result.1, (before.1, result.2))) <$> ((Pqxdh.Bytes →ₒ Output).randomOracle point).run before.2

/-- Projecting the two private tables reads exactly the cache selected by this full literal input. -/
theorem join_read (selected : Pqxdh.Bytes → Bool) (before : State) (point : Pqxdh.Bytes) :
    join selected before point = if selected point then before.1 point else before.2 point := rfl

/-- A selected-side cache write changes exactly its one original full-input cell. -/
theorem join_left (selected : Pqxdh.Bytes → Bool) (before : State) (point : Pqxdh.Bytes) (answer : Output)
    (inside : selected point = true) :
    join selected (before.1.cacheQuery point answer, before.2) = (join selected before).cacheQuery point answer := by
  apply QueryCache.ext
  intro key
  by_cases same : key = point
  · subst key
    simp only [join_read, inside, ite_true, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    simp only [join_read]
    split
    · exact QueryCache.cacheQuery_of_ne _ _ same
    · rfl

/-- A nonselected write changes its own original cell while retaining every selected hidden table entry. -/
theorem join_right (selected : Pqxdh.Bytes → Bool) (before : State) (point : Pqxdh.Bytes) (answer : Output)
    (outside : selected point = false) :
    join selected (before.1, before.2.cacheQuery point answer) = (join selected before).cacheQuery point answer := by
  apply QueryCache.ext
  intro key
  by_cases same : key = point
  · subst key
    simp only [join_read, outside, Bool.false_eq_true, ite_false, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    simp only [join_read]
    split
    · rfl
    · exact QueryCache.cacheQuery_of_ne _ _ same

/-- Each actual coin or adaptive key query has the literal original lazy-table reply and complete merged postcache. -/
theorem query_source (selected : Pqxdh.Bytes → Bool) (query : Spec.Domain) (before : State) :
    Prod.map id (join selected) <$> (handler selected query).run before =
      (PqxdhRegistrationJointKemSecondEntry.lazyImpl query).run (join selected before) := by
  cases query with
  | inl coin =>
      simp only [handler, StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
      rfl
  | inr point =>
      cases inside : selected point with
      | false =>
          have lookup : join selected before point = before.2 point := by simp only [join_read, inside, Bool.false_eq_true, ite_false]
          change Prod.map id (join selected) <$> (if selected point then _ else _) =
            ((Pqxdh.Bytes →ₒ Output).randomOracle point).run (join selected before)
          rw [inside]
          simp only [Bool.false_eq_true, ite_false, Functor.map_map, Prod.map_def, id_eq]
          cases found : before.2 point with
          | some answer =>
              rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ (lookup.trans found), map_pure]
          | none =>
              rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ (lookup.trans found)]
              simp only [Functor.map_map]
              congr 1
              funext answer
              rw [join_right selected before point answer inside]
      | true =>
          have lookup : join selected before point = before.1 point := by simp only [join_read, inside, ite_true]
          change Prod.map id (join selected) <$> (if selected point then _ else _) =
            ((Pqxdh.Bytes →ₒ Output).randomOracle point).run (join selected before)
          rw [inside]
          simp only [ite_true, Functor.map_map, Prod.map_def, id_eq]
          cases found : before.1 point with
          | some answer =>
              rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ (lookup.trans found), map_pure]
          | none =>
              rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ (lookup.trans found)]
              simp only [Functor.map_map]
              congr 1
              funext answer
              rw [join_left selected before point answer inside]

/-- The entire adaptive G2 table game retains its original full-input cache when selected and nonselected cells are stored independently. -/
theorem program_source (selected : Pqxdh.Bytes → Bool) (work : OracleComp Spec Value) (before : State) :
    Prod.map id (join selected) <$> (simulateQ (handler selected) work).run before =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run (join selected before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query_source selected query before, bind_map_left]
      exact bind_congr fun reached => ih reached.1 reached.2

end BeaconcryptCore.Computational.RegistrationNativeG3Partition
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Partition.join_read' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Partition.join_read
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Partition.join_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Partition.join_left
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Partition.join_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Partition.join_right
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Partition.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Partition.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Partition.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Partition.program_source
