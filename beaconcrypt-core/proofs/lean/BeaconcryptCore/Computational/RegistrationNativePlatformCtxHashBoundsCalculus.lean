-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore
/-! Adaptive physical-hash resource laws for the actual two-state source callback language. Every reached native/P state is retained and each source query is charged only for its real callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus
open RegistrationNativePlatformCtxLeafHashBounds (Bounded)
open RegistrationNativePlatformCtxRunner (M)
variable {Local Platform A B : Type}

/-- Pure local outcomes contribute no shared hash requests. -/
theorem pure_bound (value : A) (cap : Nat) : Bounded (pure value : M Local Platform A) cap :=
  fun _ _ => isQueryBoundP_pure _ _ _

/-- Sequencing sums the real callback allowances in their reached full native/P states. -/
theorem bind_bound (work : M Local Platform A) (next : A → M Local Platform B)
    (first later : Nat) (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro before previous
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded before previous) (fun result _ => rest result.1.1 result.1.2 result.2)

/-- Every branch of an arbitrary source tree consumes only the literal predicate-selected callback bill. -/
theorem program_bound {I : Type} {queries : OracleSpec I} (selected : I → Prop) [DecidablePred selected]
    (callback : QueryImpl queries (M Local Platform))
    (steps : ∀ query, Bounded (callback query) (if selected query then 1 else 0))
    (work : OracleComp queries A) (cap : Nat) (bounded : work.IsQueryBoundP selected cap) :
    Bounded (simulateQ callback work) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => simpa only [simulateQ_pure] using pure_bound (Local := Local) (Platform := Platform) value cap
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

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual SDK World lens retains the exact Local hash bill. -/
theorem sdk_world_bound {n : Nat} (work : M (RegistrationServerRootCompiler.Local n) Platform A)
    (cap : Nat) (bounded : Bounded work cap) :
    Bounded (RegistrationNativePlatformCtxSdk.world work) cap := by
  intro before previous
  simpa only [RegistrationNativePlatformCtxSdk.world, RegistrationNativePlatformServerSdk.world, StateT.run,
    state_map_apply, isQueryBoundP_map_iff] using bounded before.world previous
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.pure_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.sdk_world_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus.sdk_world_bound
