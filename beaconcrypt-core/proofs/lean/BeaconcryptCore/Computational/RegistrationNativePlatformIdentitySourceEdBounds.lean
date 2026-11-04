-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds
/-! Structural attached Ed signing bills retain all opaque-owner, environment and external platform state. Hashes, KEM operations and independent sampling contribute zero; only the exact indexed signing query is counted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds
open RegistrationNativePlatformIdentityProgram (M Spec)
variable {n : Nat} {KemSK Auxiliary Platform A B : Type} {source : RegistrationNativeMldsa.Source}

def IsSign : (Spec n KemSK).Domain → Prop
  | .inl _ => False
  | .inr query => RegistrationNativePlatformIdentityFrontendEdBounds.IsSign (KemSK := KemSK) query
instance : DecidablePred (IsSign (n := n) (KemSK := KemSK)) := fun query => by
  cases query with
  | inl query => simp only [IsSign]; infer_instance
  | inr query => simp only [IsSign]; infer_instance

def Bounded (work : M n KemSK Auxiliary Platform source A) (cap : Nat) : Prop :=
  ∀ owners env previous, (((work.run owners).run env).run previous).IsQueryBoundP (IsSign (KemSK := KemSK)) cap

theorem pure_bound (value : A) (cap : Nat) : Bounded (pure value : M n KemSK Auxiliary Platform source A) cap :=
  fun _ _ _ => isQueryBoundP_pure _ _ _

theorem bind_bound (work : M n KemSK Auxiliary Platform source A) (next : A → M n KemSK Auxiliary Platform source B)
    (first later : Nat) (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro owners env previous
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded owners env previous) (fun result _ => rest result.1.1.1 result.1.1.2 result.1.2 result.2)

theorem native_bound (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source A) (cap : Nat)
    (bounded : RegistrationNativePlatformIdentityFrontendEdBounds.Bounded work cap) :
    Bounded (RegistrationNativePlatformIdentityProgram.native (Platform := Platform) work) cap := by
  intro owners env previous
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run, isQueryBoundP_map_iff]
  apply (bounded owners env).simulateQ_of_step
  · intro query active
    simp [RegistrationNativePlatformIdentityProgram.nativeLift, IsSign, active]
  · intro query inactive
    simp [RegistrationNativePlatformIdentityProgram.nativeLift, IsSign, inactive]

theorem external_bound (work : StateT Platform ProbComp A) :
    Bounded (RegistrationNativePlatformIdentityProgram.external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) 0 := by
  intro owners env previous
  simp only [RegistrationNativePlatformIdentityProgram.external, StateT.run, isQueryBoundP_map_iff]
  apply (isQueryBoundP_false (work.run previous) 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativePlatformIdentityProgram.externalLift, IsSign]

theorem get_bound : Bounded (get : M n KemSK Auxiliary Platform source (RegistrationNativeIdentityFrontend.State source)) 0 :=
  fun _ _ _ => isQueryBoundP_pure _ _ _
theorem program_bound {I : Type} {queries : OracleSpec I} (selected : I → Prop) [DecidablePred selected]
    (callback : QueryImpl queries (M n KemSK Auxiliary Platform source))
    (steps : ∀ query, Bounded (callback query) (if selected query then 1 else 0))
    (work : OracleComp queries A) (cap : Nat) (bounded : work.IsQueryBoundP selected cap) :
    Bounded (simulateQ callback work) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => simpa only [simulateQ_pure] using pure_bound (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) value cap
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_bind, simulateQ_spec_query]
    have combined := bind_bound (callback query) (fun value => simulateQ callback (next value))
      (if selected query then 1 else 0) (if selected query then cap - 1 else cap)
      (steps query) (fun value => ih value _ (bounded.2 value))
    have total : (if selected query then 1 else 0) + (if selected query then cap - 1 else cap) = cap := by
      by_cases active : selected query
      · have positive := bounded.1
        simp only [active, not_true_eq_false, false_or] at positive
        simp only [active, ite_true]
        omega
      · simp only [active, ite_false, Nat.zero_add]
    simpa only [total] using combined
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.pure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.external_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.external_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.get_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.get_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds.program_bound
