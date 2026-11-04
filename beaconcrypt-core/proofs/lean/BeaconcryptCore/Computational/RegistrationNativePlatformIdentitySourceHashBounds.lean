-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendHashBounds
/-! The genuine opaque-owner source language adds stateful platform work without adding shared hashes. Native source hash allowances transfer exactly into its separate external/native branches and adaptive continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds
open RegistrationNativePlatformIdentityProgram (M Spec)
variable {n : Nat} {KemSK Auxiliary Platform A B : Type} {source : RegistrationNativeMldsa.Source}

def IsHash : (Spec n KemSK).Domain → Prop
  | .inl _ => False
  | .inr query => RegistrationNativePlatformIdentityFrontendHashBounds.IsHash (KemSK := KemSK) query
instance : DecidablePred (IsHash (n := n) (KemSK := KemSK)) := fun query => by
  cases query with
  | inl query => simp only [IsHash]; infer_instance
  | inr query => simp only [IsHash]; infer_instance

def Bounded (work : M n KemSK Auxiliary Platform source A) (cap : Nat) : Prop :=
  ∀ owners env previous, (((work.run owners).run env).run previous).IsQueryBoundP (IsHash (KemSK := KemSK)) cap

/-- Pure source results retain every owner, environment and P field at zero extra hash cost. -/
theorem pure_bound (value : A) (cap : Nat) : Bounded (pure value : M n KemSK Auxiliary Platform source A) cap :=
  fun _ _ _ => isQueryBoundP_pure _ _ _

/-- Literal adaptive source sequencing sums hash calls across its actual reached poststate. -/
theorem bind_bound (work : M n KemSK Auxiliary Platform source A) (next : A → M n KemSK Auxiliary Platform source B)
    (first later : Nat) (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro owners env previous
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded owners env previous) (fun result _ => rest result.1.1.1 result.1.1.2 result.1.2 result.2)

/-- The actual native tree is embedded without changing any of its shared hash calls. -/
theorem native_bound (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source A) (cap : Nat)
    (bounded : RegistrationNativePlatformIdentityFrontendHashBounds.Bounded work cap) :
    Bounded (RegistrationNativePlatformIdentityProgram.native (Platform := Platform) work) cap := by
  intro owners env previous
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run, isQueryBoundP_map_iff]
  apply (bounded owners env).simulateQ_of_step
  · intro query active
    simp [RegistrationNativePlatformIdentityProgram.nativeLift, IsHash, active]
  · intro query inactive
    simp [RegistrationNativePlatformIdentityProgram.nativeLift, IsHash, inactive]

/-- Arbitrary platform actions preserve their own P effects and contribute no native shared hash. -/
theorem external_bound (work : StateT Platform ProbComp A) :
    Bounded (RegistrationNativePlatformIdentityProgram.external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) 0 := by
  intro owners env previous
  simp only [RegistrationNativePlatformIdentityProgram.external, StateT.run, isQueryBoundP_map_iff]
  apply (isQueryBoundP_false (work.run previous) 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativePlatformIdentityProgram.externalLift, IsHash]

/-- Reading the source owner roster issues no primitive operation. -/
theorem get_bound : Bounded (get : M n KemSK Auxiliary Platform source (RegistrationNativeIdentityFrontend.State source)) 0 :=
  fun _ _ _ => isQueryBoundP_pure _ _ _
/-- Every source request is charged only for its literal callback, including all adaptive reply branches. -/
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
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.pure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.external_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.external_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.get_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.get_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds.program_bound
