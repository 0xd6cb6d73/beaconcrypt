-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked

/-! A clean audit on the same unchecked native execution derives every reached local preparation check. The original adaptive client and its full native flags are therefore equal to the flag-enforcing source, with only the private false marker erased. Normalized support supplies an actual continuation witness; no equality of games or readiness premise is imported. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedService (Flags)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeG3NativeChecked (Spec State bad unchecked)
variable {Value : Type}
variable (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)

/-- A native unprepared-demand marker remains true through every subsequent actual adaptive callback. -/
theorem sticky (work : OracleComp Spec Value) (before : State) (marked : before.2 = true)
    (result : Value × State) (supported : result ∈ support ((simulateQ (unchecked source input inside) work).run before)) : result.2.2 = true := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact marked
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, later⟩ := supported
      have flagged := RegistrationNativeG3NativeChecked.query_flag source input inside query before middle first
      rw [marked, Bool.true_or] at flagged
      exact ih middle.1 middle.2 flagged later

private theorem first_good (query : Spec.Domain) (next : Spec.Range query → OracleComp Spec Value) (before : Flags)
    (clean : ∀ result ∈ support ((simulateQ (unchecked source input inside)
      ((((Spec.query query) : OracleComp Spec (Spec.Range query))) >>= next)).run (before, false)), result.2.2 = false) :
    bad input query before = false := by
  cases firstBad : bad input query before with
  | false => rfl
  | true =>
      obtain ⟨result, supported⟩ := OracleComp.support_nonempty ((simulateQ (unchecked source input inside)
        ((((Spec.query query) : OracleComp Spec (Spec.Range query))) >>= next)).run (before, false))
      have finalClean := clean result supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, later⟩ := supported
      have flagged := RegistrationNativeG3NativeChecked.query_flag source input inside query (before, false) middle first
      simp only [Bool.false_or, firstBad] at flagged
      have finalMarked := sticky source input inside (next middle.1) middle.2 flagged result later
      rw [finalClean] at finalMarked
      cases finalMarked

/-- A clean same-run unchecked audit yields the exact full flags-preserving source equation for the original adaptive native service. -/
theorem program_source (work : OracleComp Spec Value) (before : Flags)
    (clean : ∀ result ∈ support ((simulateQ (unchecked source input inside) work).run (before, false)), result.2.2 = false) :
    (simulateQ (unchecked source input inside) work).run (before, false) =
      (fun result => (result.1, (result.2, false))) <$>
        (simulateQ (RegistrationNativeG3KeyService.direct source input inside) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      have good := first_good source input inside query next before clean
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [RegistrationNativeG3NativeChecked.query_source source input inside query before false good]
      simp only [bind_map_left, map_bind]
      apply bind_congr_of_forall_mem_support
      intro reached actual
      apply ih reached.1 reached.2
      intro result later
      apply clean result
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      refine ⟨(reached.1, (reached.2, false)), ?_, later⟩
      rw [RegistrationNativeG3NativeChecked.query_source source input inside query before false good, support_map]
      exact Set.mem_image_of_mem _ actual

/-- Erasing only the derived false audit marker leaves the complete original result and native descriptor flags. -/
theorem erase_source (work : OracleComp Spec Value) (before : Flags)
    (clean : ∀ result ∈ support ((simulateQ (unchecked source input inside) work).run (before, false)), result.2.2 = false) :
    Prod.map id Prod.fst <$> (simulateQ (unchecked source input inside) work).run (before, false) =
      (simulateQ (RegistrationNativeG3KeyService.direct source input inside) work).run before := by
  rw [program_source source input inside work before clean]
  simp only [Functor.map_map, Prod.map_def, id_eq, id_map']

/-- The actual two-pass retained/phase compiler equals the unchecked native service after its same-run audit is discharged. -/
theorem client_source (work : OracleComp Spec Value)
    (clean : ∀ result ∈ support ((simulateQ (unchecked source input inside) work).run ((fun _ => false), false)), result.2.2 = false) :
    RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work)
      RegistrationNativeKeyPhases.emptyMeta =
        Prod.fst <$> (simulateQ (unchecked source input inside) work).run ((fun _ => false), false) := by
  rw [RegistrationNativeG3KeyServiceInlining.client_source, StateT.run'_eq]
  have same := congrArg (Functor.map Prod.fst) (erase_source source input inside work (fun _ => false) clean)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same.symm

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.sticky
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.erase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.erase_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun.client_source
