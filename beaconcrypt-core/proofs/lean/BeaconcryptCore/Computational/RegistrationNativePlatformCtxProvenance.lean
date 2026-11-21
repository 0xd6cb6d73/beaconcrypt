-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend
/-! The physical CTX backend retains exact chronological queried inputs and has no cache entry outside that journal from empty startup. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance
open RegistrationNativePlatformCtxBackend
variable {A : Type}

def Provenance (before : State) : Prop :=
  ∀ bytes, before.1 ((), bytes) ≠ none → bytes ∈ before.2

theorem empty : Provenance (∅, []) := by
  intro bytes present
  exact False.elim (present rfl)

theorem physical (bytes : Pqxdh.Bytes) (before : State) (valid : Provenance before)
    (after : (CtxRomAuth.CtxDigest × Nat) × State)
    (supported : after ∈ support ((RegistrationNativePlatformCtxBackend.physical bytes).run before)) :
    Provenance after.2 := by
  have marginal : (after.1.1, after.2.1) ∈ support ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.1) := by
    rw [← physical_forget bytes before, support_map]
    exact ⟨after, supported, rfl⟩
  have journal := physical_journal bytes before after supported
  intro input present
  rw [journal, List.mem_append, List.mem_singleton]
  cases CtxRomAuth.ctxRandomOracle_cache_origin ((), bytes) before.1 (after.1.1, after.2.1) marginal ((), input) present with
  | inl old => exact Or.inl (valid input old)
  | inr actual => exact Or.inr (congrArg Prod.snd actual)

theorem query (request : Spec.Domain) (before : State) (valid : Provenance before)
    (after : Spec.Range request × State)
    (supported : after ∈ support ((implementation request).run before)) :
    Provenance after.2 := by
  cases request with
  | inl bytes => exact physical bytes before valid after supported
  | inr coin =>
    simp only [implementation, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _member, rfl⟩ := supported
    exact valid

/-- Every cached address in an arbitrary adaptive backend computation has an actual earlier journal occurrence. -/
theorem complete (work : OracleComp Spec A) (before : State) (valid : Provenance before)
    (after : A × State) (supported : after ∈ support ((simulateQ implementation work).run before)) :
    Provenance after.2 := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst after
    exact valid
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind, Set.mem_iUnion] at supported
    obtain ⟨middle, member, tail⟩ := supported
    exact ih middle.1 middle.2 (query request before valid middle member) after tail
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance.complete
