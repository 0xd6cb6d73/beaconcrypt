-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyCompile

/-! The adapter inserts exactly one metadata HMAC transport per native create. All other command classes retain their original caps, including secrecy/record/accept/create bounds. These are all-reply structural bounds, and metadata transport invokes no cryptographic HMAC. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyBounds
open RegistrationNativeEntropyCompile (compiler compile modeO modeP)
open PqxdhDeploymentInterface (Mode Budget)
variable {Value : Type}

def budget (native : Budget) : Budget := { native with hmac := native.hmac + native.create }

def sourceClass (kind : Fin 14) (query : RegistrationNativeInterface.Query) : Prop :=
  RegistrationNativeInterface.queryClass query = kind ∨
    (kind = 6 ∧ RegistrationNativeInterface.queryClass query = 1)

instance (kind : Fin 14) : DecidablePred (sourceClass kind) := fun query =>
  inferInstanceAs (Decidable (RegistrationNativeInterface.queryClass query = kind ∨
    (kind = 6 ∧ RegistrationNativeInterface.queryClass query = 1)))

private theorem union_bound {I Result : Type} {spec : OracleSpec I}
    (first second : I → Prop) [DecidablePred first] [DecidablePred second]
    (work : OracleComp spec Result) (left right : Nat)
    (leftBound : work.IsQueryBoundP first left) (rightBound : work.IsQueryBoundP second right) :
    work.IsQueryBoundP (fun query => first query ∨ second query) (left + right) := by
  induction work using OracleComp.inductionOn generalizing left right with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at leftBound rightBound ⊢
      constructor
      · by_cases a : first query <;> by_cases b : second query <;> simp_all only [not_true_eq_false,
          not_false_eq_true, false_or, or_false, true_or, or_true] <;> omega
      · intro reply
        apply (ih reply _ _ (leftBound.2 reply) (rightBound.2 reply)).mono
        by_cases a : first query <;> by_cases b : second query <;>
          simp_all only [ite_true, ite_false, true_or, or_true, false_or, or_false,
            not_true_eq_false, not_false_eq_true] <;> omega

set_option maxHeartbeats 1000000 in
/-- Each native query has the exact selective old-class cost, including its one metadata transport. -/
theorem query_bound (mode : Mode) (query : RegistrationNativeInterface.Query) (kind : Fin 14) :
    (compiler mode query).IsQueryBoundP (fun old => PqxdhDeploymentInterface.queryClass old = kind)
      (if sourceClass kind query then 1 else 0) := by
  classical
  fin_cases kind
  all_goals cases mode
  all_goals rcases query with (coin | command) | secrecy
  all_goals first
    | cases command <;> simp [compiler, modeO, modeP, sourceClass, RegistrationNativeInterface.queryClass,
        RegistrationNativeInterface.eraseQuery, RegistrationNativeInterface.eraseCore,
        RegistrationNativeInterface.eraseCommand, PqxdhDeploymentInterface.queryClass,
        isQueryBoundP_query_bind_iff, isQueryBoundP_query_iff]
    | cases secrecy <;> simp [compiler, modeO, modeP, sourceClass, RegistrationNativeInterface.queryClass,
        RegistrationNativeInterface.eraseQuery, PqxdhDeploymentInterface.queryClass,
        isQueryBoundP_query_iff]
    | simp [compiler, modeO, modeP, sourceClass, RegistrationNativeInterface.queryClass,
        RegistrationNativeInterface.eraseQuery, RegistrationNativeInterface.eraseCore,
        PqxdhDeploymentInterface.queryClass, isQueryBoundP_query_iff]

/-- Native source budgets charge the extra transport only to the old HMAC command class. -/
theorem source_bound (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (native : Budget) (bounded : RegistrationNativeInterface.Respects native work) (kind : Fin 14) :
    work.IsQueryBoundP (sourceClass kind) ((budget native).cap kind) := by
  classical
  by_cases hmac : kind = 6
  · subst kind
    have combined := union_bound (fun query => RegistrationNativeInterface.queryClass query = 6)
      (fun query => RegistrationNativeInterface.queryClass query = 1) work _ _ (bounded 6) (bounded 1)
    apply (isQueryBoundP_congr_pred
      (p := fun query => RegistrationNativeInterface.queryClass query = 6 ∨
        RegistrationNativeInterface.queryClass query = 1) (p' := sourceClass 6)
      (fun query => by simp only [sourceClass, true_and])).mp
    simpa [budget, Budget.cap] using combined
  · have unchanged : sourceClass kind = (fun query => RegistrationNativeInterface.queryClass query = kind) := by
      funext query
      simp only [sourceClass, hmac, false_and, or_false]
    have same : (budget native).cap kind = native.cap kind := by
      fin_cases kind <;> simp_all [budget, Budget.cap]
    simpa only [unchanged, same] using bounded kind

/-- The complete adaptive native adversary respects the transported budget on every reply path. -/
theorem compile_respects (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (native : Budget) (bounded : RegistrationNativeInterface.Respects native work) :
    (budget native).Respects (compile mode work) := by
  intro kind
  exact RawCtxSourceOpen.simulate_bound (compiler mode) (sourceClass kind)
    (fun old => PqxdhDeploymentInterface.queryClass old = kind) work _
    (source_bound mode work native bounded kind) (fun query => query_bound mode query kind)

/-- Record sends, raw receives, fresh-byte allowance, creation capacity and the accept/create target product retain their exact original values. -/
theorem retained_budget (native : Budget) (bounds : PqxdhDeploymentInterface.FreshBounds) :
    (budget native).sends = native.sends ∧ (budget native).receives = native.receives ∧
      (budget native).freshBytes bounds = native.freshBytes bounds ∧
      (budget native).capacity = native.capacity ∧ (budget native).targets = native.targets :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeEntropyBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.query_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.source_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.compile_respects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.compile_respects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.retained_budget' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyBounds.retained_budget
