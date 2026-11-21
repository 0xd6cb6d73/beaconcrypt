-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked

/-! The native preparation audit is closed under an arbitrary actual stateful key interpretation. Both sides retain the same external state, native flags and all callback results. Normalized oracle support and the sticky same-run audit derive every reached local preparation check; no open-oracle cleanliness or game equality is inferred from a closed execution. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedService (Flags)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeKeyCompiler (KeySpec)
open RegistrationNativeG3NativeChecked (Spec bad)
variable {Index Cache Value : Type} {ambient : OracleSpec Index}

abbrev DirectState (Cache : Type) := Flags × Cache
abbrev State (Cache : Type) := (Flags × Bool) × Cache

def addMarker (marked : Bool) (before : DirectState Cache) : State Cache := ((before.1, marked), before.2)

def direct (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) :
    QueryImpl Spec (StateT (DirectState Cache) (OracleComp ambient)) :=
  (outer.mapStateTBase (RegistrationNativeG3KeyService.direct source input inside)).flattenStateT

def unchecked (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) :
    QueryImpl Spec (StateT (State Cache) (OracleComp ambient)) :=
  (outer.mapStateTBase (RegistrationNativeG3NativeChecked.unchecked source input inside)).flattenStateT

/-- The actual closed callback preserves all external state and replies when its same-run native demand audit is clean. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) (query : Spec.Domain)
    (flags : Flags) (marked : Bool) (cache : Cache) (good : bad input query flags = false) :
    (unchecked source input inside outer query).run ((flags, marked), cache) =
      Prod.map id (addMarker marked) <$> (direct source input inside outer query).run (flags, cache) := by
  simp only [unchecked, direct, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rw [RegistrationNativeG3NativeChecked.query_source source input inside query flags marked good]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq, addMarker]

/-- The audit is computed from the actual pre-query native flags even after all key callbacks and external state have been interpreted. -/
theorem query_flag (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) (query : Spec.Domain)
    (before : State Cache) (result : Spec.Range query × State Cache)
    (supported : result ∈ support ((unchecked source input inside outer query).run before)) :
    result.2.1.2 = (before.1.2 || bad input query before.1.1) := by
  rcases before with ⟨auditBefore, cache⟩
  simp only [unchecked, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  have opened : reached.1 ∈ support ((RegistrationNativeG3NativeChecked.unchecked source input inside query).run auditBefore) := by
    apply OracleComp.support_simulateQ_run'_subset outer _ cache
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst actual
  exact RegistrationNativeG3NativeChecked.query_flag source input inside query auditBefore reached.1 opened

/-- Later actual closed callbacks cannot clear a native valid-but-unprepared demand marker. -/
theorem sticky (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) (work : OracleComp Spec Value)
    (before : State Cache) (flagged : before.1.2 = true) (result : Value × State Cache)
    (supported : result ∈ support ((simulateQ (unchecked source input inside outer) work).run before)) : result.2.1.2 = true := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact flagged
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, later⟩ := supported
      have marked := query_flag source input inside outer query before middle first
      rw [flagged, Bool.true_or] at marked
      exact ih middle.1 middle.2 marked later

variable [∀ query, Nonempty (ambient.Range query)]

private theorem first_good (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) (query : Spec.Domain)
    (next : Spec.Range query → OracleComp Spec Value) (flags : Flags) (cache : Cache)
    (clean : ∀ result ∈ support ((simulateQ (unchecked source input inside outer)
      ((((Spec.query query) : OracleComp Spec (Spec.Range query))) >>= next)).run ((flags, false), cache)), result.2.1.2 = false) :
    bad input query flags = false := by
  cases firstBad : bad input query flags with
  | false => rfl
  | true =>
      obtain ⟨result, supported⟩ := OracleComp.support_nonempty ((simulateQ (unchecked source input inside outer)
        ((((Spec.query query) : OracleComp Spec (Spec.Range query))) >>= next)).run ((flags, false), cache))
      have finalClean := clean result supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, later⟩ := supported
      have flagged := query_flag source input inside outer query ((flags, false), cache) middle first
      simp only [Bool.false_or, firstBad] at flagged
      have finalMarked := sticky source input inside outer (next middle.1) middle.2 flagged result later
      rw [finalClean] at finalMarked
      cases finalMarked

/-- A clean actual closed audit derives the complete original flags-preserving source equation under that same external stateful key interpretation. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) (work : OracleComp Spec Value) (flags : Flags) (cache : Cache)
    (clean : ∀ result ∈ support ((simulateQ (unchecked source input inside outer) work).run ((flags, false), cache)), result.2.1.2 = false) :
    (simulateQ (unchecked source input inside outer) work).run ((flags, false), cache) =
      Prod.map id (addMarker false) <$> (simulateQ (direct source input inside outer) work).run (flags, cache) := by
  induction work using OracleComp.inductionOn generalizing flags cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq, addMarker]
  | query_bind query next ih =>
      have good := first_good source input inside outer query next flags cache clean
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [query_source source input inside outer query flags false cache good]
      simp only [bind_map_left, map_bind, Prod.map_def, id_eq, addMarker]
      apply bind_congr_of_forall_mem_support
      intro reached actual
      apply ih reached.1 reached.2.1 reached.2.2
      intro result later
      apply clean result
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      refine ⟨(reached.1, ((reached.2.1, false), reached.2.2)), ?_, later⟩
      rw [query_source source input inside outer query flags false cache good, support_map]
      exact Set.mem_image_of_mem _ actual

omit [∀ query, Nonempty (ambient.Range query)] in
private theorem direct_values_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) (work : OracleComp Spec Value) (flags : Flags) (cache : Cache) :
    (simulateQ outer ((simulateQ (RegistrationNativeG3KeyService.direct source input inside) work).run' flags)).run cache =
      (fun result => (result.1, result.2.2)) <$> (simulateQ (direct source input inside outer) work).run (flags, cache) := by
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT outer
    (RegistrationNativeG3KeyService.direct source input inside) work flags cache
  have mapped := congrArg (Functor.map (fun result => (result.1.1, result.2))) nested
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
    direct, Prod.map_def, id_eq] using mapped

/-- The original retained/phase compiler and the unchecked native service have the same complete external-state result once that actual closed audit is discharged. -/
theorem client_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (outer : QueryImpl KeySpec (StateT Cache (OracleComp ambient))) (work : OracleComp Spec Value) (cache : Cache)
    (clean : ∀ result ∈ support ((simulateQ (unchecked source input inside outer) work).run (((fun _ => false), false), cache)), result.2.1.2 = false) :
    (simulateQ outer (RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work)
      RegistrationNativeKeyPhases.emptyMeta)).run cache =
        (fun result => (result.1, result.2.2)) <$>
          (simulateQ (unchecked source input inside outer) work).run (((fun _ => false), false), cache) := by
  rw [RegistrationNativeG3KeyServiceInlining.client_source, direct_values_source]
  have same := congrArg (Functor.map (fun result => (result.1, result.2.2)))
    (program_source source input inside outer work (fun _ => false) cache clean)
  simpa only [Functor.map_map, Prod.map_def, id_eq, addMarker] using same.symm

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.query_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.query_flag
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.sticky
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClosed.client_source
