-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend

/-! Real Server agreement primitives do not generate or decapsulate a native owner key and never prepare a root capability. Their full adaptive execution therefore retains the entire private owner pool and remaining private service state, including every optional callback failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReferenceFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceBackend (State backend)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}

private theorem ordinary_frame (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : RegistrationAgreementExecutor.Request)
    (notKem : RegistrationNativeKemReferenceCompiler.NonEncapsulation query) (before : State n KemSK Extra)
    (result : RegistrationAgreementExecutor.Spec.Range query × State n KemSK Extra)
    (reached : result ∈ support ((backend setup checks callbacks query).run before)) :
    result.2.2.pool = before.2.pool ∧ result.2.2.extra = before.2.extra := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (simulateQ (implementation setup callbacks)
      ((RegistrationNativeKemReferenceCompiler.backend setup checks query).run before.1)).run before.2) at reached
  rw [RegistrationNativeKemReferenceEffects.backend_ordinary setup checks callbacks query notKem before.1 before.2] at reached
  simp only [Functor.map_map, support_map] at reached
  obtain ⟨inner, _, rfl⟩ := reached
  exact ⟨rfl, rfl⟩

private theorem encapsulation_frame (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (key : core.option.Option (Std.Array U8 1184#usize)) (before : State n KemSK Extra)
    (result : RegistrationAgreementExecutor.Spec.Range (.encapsulate key) × State n KemSK Extra)
    (reached : result ∈ support ((backend setup checks callbacks (.encapsulate key)).run before)) :
    result.2.2.pool = before.2.pool ∧ result.2.2.extra = before.2.extra := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (simulateQ (implementation setup callbacks)
      ((RegistrationNativeKemReferenceCompiler.backend setup checks (.encapsulate key)).run before.1)).run before.2) at reached
  rw [RegistrationNativeKemReferenceEncapsulation.source setup checks callbacks key before.1 before.2] at reached
  simp only [Functor.map_map, support_map] at reached
  obtain ⟨inner, _, rfl⟩ := reached
  exact ⟨rfl, rfl⟩

/-- Each real open Server primitive keeps the complete native KEM pool and private service state. -/
theorem query_frame (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : RegistrationAgreementExecutor.Request) (before : State n KemSK Extra)
    (result : RegistrationAgreementExecutor.Spec.Range query × State n KemSK Extra)
    (reached : result ∈ support ((backend setup checks callbacks query).run before)) :
    result.2.2.pool = before.2.pool ∧ result.2.2.extra = before.2.extra := by
  cases query with
  | encapsulate key => exact encapsulation_frame setup checks callbacks key before result reached
  | convertPublic key => exact ordinary_frame setup checks callbacks (.convertPublic key) trivial before result reached
  | convertSecret role => exact ordinary_frame setup checks callbacks (.convertSecret role) trivial before result reached
  | generate role => exact ordinary_frame setup checks callbacks (.generate role) trivial before result reached
  | decapsulate ciphertext => exact ordinary_frame setup checks callbacks (.decapsulate ciphertext) trivial before result reached
  | dh request => exact ordinary_frame setup checks callbacks (.dh request) trivial before result reached
  | root request => exact ordinary_frame setup checks callbacks (.root request) trivial before result reached

/-- Arbitrary adaptive continuations retain that same whole private frame without a source-program simulation premise. -/
theorem program_frame (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : State n KemSK Extra)
    (result : Value × State n KemSK Extra)
    (reached : result ∈ support ((simulateQ (backend setup checks callbacks) work).run before)) :
    result.2.2.pool = before.2.pool ∧ result.2.2.extra = before.2.extra := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨step, first, tail⟩ := reached
      obtain ⟨poolFirst, extraFirst⟩ := query_frame setup checks callbacks query before step first
      obtain ⟨poolTail, extraTail⟩ := ih step.1 step.2 result tail
      exact ⟨poolTail.trans poolFirst, extraTail.trans extraFirst⟩

end BeaconcryptCore.Computational.RegistrationNativeKemReferenceFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceFrame.query_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceFrame.query_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceFrame.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceFrame.program_frame
