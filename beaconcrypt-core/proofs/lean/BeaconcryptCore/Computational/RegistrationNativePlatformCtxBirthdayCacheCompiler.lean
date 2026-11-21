-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler
/-! Structural cache collision containment for the literal physical CTX compiler. Instrumentation retains the exact count-bearing hash replies, complete input journal and shared cache; only the chronological digest history is added. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler
open PqxdhRecordFactsCollision (History interpreter)
open PqxdhRecordFactsCollisionCache (Good Collision)
open RegistrationNativePlatformCtxBackend (Spec State)
variable {A : Type}

/-- Reassociate the compiler's actual cache/journal state with the added statistical history. -/
def flatten (result : (A × State) × History CtxRomAuth.CtxDigest) :
    A × (State × History CtxRomAuth.CtxDigest) := (result.1.1, result.1.2, result.2)

noncomputable def instrumented : QueryImpl Spec (StateT (State × History CtxRomAuth.CtxDigest) ProbComp) :=
  fun query before => flatten <$>
    (simulateQ interpreter ((RegistrationNativePlatformCtxBirthdayCompiler.compiler query).run before.1)).run before.2

/-- The actual cache is the first coordinate of the complete physical backend state. -/
def StructuralGood (before : State × History CtxRomAuth.CtxDigest) : Prop :=
  Good (fun _ => true) (before.1.1, before.2)

/-- An actual empty/singleton physical cache has a clean structural history with at most one retained earlier digest, independently of its input journal. -/
theorem warm_good (before : State) (warm : RegistrationNativePlatformCtxBirthdayCache.Warm before.1) :
    ∃ history : History CtxRomAuth.CtxDigest, StructuralGood (before, history) ∧ history.bad = false ∧
      history.targets.length + history.ordinary.length ≤ 1 := by
  rcases warm with empty | ⟨input, digest, singleton⟩
  · refine ⟨History.empty, ?_, rfl, by simp [History.empty]⟩
    change Good (fun _ => true) (before.1, History.empty)
    rw [empty]
    exact PqxdhRecordFactsCollisionCache.initial_good _
  · refine ⟨⟨[digest], [], false⟩, ?_, rfl, by simp⟩
    change Good (fun _ => true) (before.1, ⟨[digest], [], false⟩)
    rw [singleton]
    exact RegistrationNativePlatformCtxBirthdayCache.singleton_good input digest

private theorem state_map_apply {S X Y : Type} (observe : X → Y) (work : StateT S ProbComp X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem state_pure_apply {S X : Type} (value : X) (before : S) :
    (pure value : StateT S ProbComp X) before = pure (value, before) := rfl

/-- Each literal compiler query retains draw provenance and collision containment, including zero-draw hits and arbitrary public coins. -/
theorem query_good (query : Spec.Domain) (before : State × History CtxRomAuth.CtxDigest)
    (good : StructuralGood before) (result : Spec.Range query × (State × History CtxRomAuth.CtxDigest))
    (present : result ∈ support ((instrumented query).run before)) : StructuralGood result.2 := by
  cases query with
  | inl bytes =>
    simp only [instrumented, RegistrationNativePlatformCtxBirthdayCompiler.compiler, StateT.run] at present
    cases found : before.1.1 ((), bytes) with
    | none =>
      simp only [found, bind_pure_comp, simulateQ_map, simulateQ_spec_query, interpreter,
        state_map_apply, bind_pure_comp, Functor.map_map, support_map] at present
      obtain ⟨digest, _drawn, rfl⟩ := present
      exact ⟨PqxdhRecordFactsCollisionCache.recorded_insert (fun _ => true) before.1.1 before.2 good.1 ((), bytes) digest,
        PqxdhRecordFactsCollisionCache.separated_insert (fun _ => true) before.1.1 before.2 good.1 good.2 ((), bytes) digest⟩
    | some digest =>
      simp only [found, simulateQ_pure, state_pure_apply, map_pure, support_pure, Set.mem_singleton_iff] at present
      exact present ▸ good
  | inr coin =>
    simp only [instrumented, RegistrationNativePlatformCtxBirthdayCompiler.compiler, StateT.run,
      bind_pure_comp, simulateQ_map, simulateQ_spec_query, interpreter, state_map_apply,
      StateT.run, bind_pure_comp, Functor.map_map, support_map] at present
    obtain ⟨reply, _drawn, rfl⟩ := present
    exact good

/-- Arbitrary adaptive backend programs preserve the structural invariant for every supported full result. -/
theorem program_good (work : OracleComp Spec A) (before : State × History CtxRomAuth.CtxDigest)
    (good : StructuralGood before) (result : A × (State × History CtxRomAuth.CtxDigest))
    (present : result ∈ support ((simulateQ instrumented work).run before)) : StructuralGood result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle instrumented StructuralGood
    (fun query current valid after supported => query_good query current valid after supported)
    work before good result present

/-- The instrumented fold is exactly the original source compiler followed by the same digest/coin interpreter. -/
theorem program_compile (work : OracleComp Spec A) (before : State × History CtxRomAuth.CtxDigest) :
    flatten <$> (simulateQ interpreter ((simulateQ RegistrationNativePlatformCtxBirthdayCompiler.compiler work).run before.1)).run before.2 =
      (simulateQ instrumented work).run before := by
  have leaves : ((interpreter (α := CtxRomAuth.CtxDigest)).mapStateTBase RegistrationNativePlatformCtxBirthdayCompiler.compiler).flattenStateT = instrumented := by
    ext query current
    rfl
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, leaves]
  simp only [Functor.map_map, flatten, Prod.eta]
  exact id_map _

/-- Every supported full source-compiler result records the actual cache in the same chronological digest history. -/
theorem compiled_good (work : OracleComp Spec A) (before : State) (history : History CtxRomAuth.CtxDigest)
    (good : StructuralGood (before, history)) (result : (A × State) × History CtxRomAuth.CtxDigest)
    (present : result ∈ support ((simulateQ interpreter ((simulateQ RegistrationNativePlatformCtxBirthdayCompiler.compiler work).run before)).run history)) :
    Good (fun _ => true) (result.1.2.1, result.2) := by
  have mapped : flatten result ∈ support ((simulateQ instrumented work).run (before, history)) := by
    rw [← program_compile, support_map]
    exact ⟨result, present, rfl⟩
  exact program_good work (before, history) good (flatten result) mapped

/-- A collision between distinct actual cache inputs is contained in this same source execution's absorbing draw flag. -/
theorem compiled_collision_detected (work : OracleComp Spec A) (before : State) (history : History CtxRomAuth.CtxDigest)
    (good : StructuralGood (before, history)) (result : (A × State) × History CtxRomAuth.CtxDigest)
    (present : result ∈ support ((simulateQ interpreter ((simulateQ RegistrationNativePlatformCtxBirthdayCompiler.compiler work).run before)).run history))
    (collision : Collision (fun _ => true) result.1.2.1) : result.2.bad = true := by
  obtain ⟨left, right, digest, different, targeted, atLeft, atRight⟩ := collision
  exact (compiled_good work before history good result present).2 left right digest different targeted atLeft atRight

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.warm_good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.warm_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.query_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.program_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.program_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.program_compile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.compiled_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.compiled_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.compiled_collision_detected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler.compiled_collision_detected
