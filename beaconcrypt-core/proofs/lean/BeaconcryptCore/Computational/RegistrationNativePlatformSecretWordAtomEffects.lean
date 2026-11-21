-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace
/-! Literal source publication effects cannot prepare or demand a root. Noninstalling source publication preserves the complete Word observer, and each actual Env installation suffix spends only its current descriptor's atom credit. Source allocation, signature, serializer, counter and returned platform effects remain in the tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativeSecretWordInterface (Spec liftLocal effect)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordAtomInstallTrace (RootFree atom count)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
open RegistrationNativePlatformPairedPublicationFree (Allowed Quiet)
variable {n : Nat} {KemSK S A : Type}

def env : QueryImpl (EnvEffects n) (OracleComp (Spec n KemSK)) := liftLocal false ∘ₛ effect
def effects : QueryImpl (RegistrationNativePlatformEffectCompiler.Spec n) (OracleComp (Spec n KemSK))
  | .inl query => env query
  | .inr coin => env (.inl coin)

/-- The effect projection is exactly the same one used by the new symbolic source build. -/
theorem embedding :
    (liftLocal (n := n) (KemSK := KemSK) false ∘ₛ RegistrationNativePlatformSecretWordBuild.wordEmbedding) ∘ₛ
      RegistrationNativePlatformSecretWordBuild.embed = effects := by
  funext query
  cases query <;> simp only [QueryImpl.apply_compose, RegistrationNativePlatformSecretWordBuild.embed,
    simulateQ_spec_query, RegistrationNativePlatformSecretWordBuild.wordEmbedding, effects, env]

/-- Every allowed noninstalling actual source leaf retains the entire chronological Word observer. -/
theorem query_neutral (query : (RegistrationNativePlatformEffectCompiler.Spec n).Domain)
    (allowed : Allowed query) (before : State) :
    (simulateQ handler (effects (KemSK := KemSK) query)).run before =
      (fun reply => (reply, before)) <$> effects query := by
  cases query with
  | inr coin => rfl
  | inl query =>
    rcases query with coin | capability
    · rfl
    · cases capability <;>
        simp only [effects, env, QueryImpl.apply_compose, effect, liftLocal, simulateQ_spec_query,
          handler, StateT.run, RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish]
      all_goals first | rfl | exact False.elim (allowed _ rfl)

/-- Adaptive noninstalling publication retains the exact source result and its same observer. -/
theorem program_neutral (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A)
    (allowed : work.AllQueriesSatisfy Allowed) (before : State) :
    (simulateQ handler (simulateQ (effects (KemSK := KemSK)) work)).run before =
      (fun reply => (reply, before)) <$> simulateQ effects work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [query_neutral query allowed.1 before, bind_map_left]
    apply bind_congr
    intro reply
    exact ih reply (allowed.2 reply)

/-- Every reached mutable source publication state retains that complete observer too. -/
theorem state_neutral (work : StateT S (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : Quiet work) (sourceBefore : S) (before : State) :
    (simulateQ handler (simulateQ (effects (KemSK := KemSK)) (work.run sourceBefore))).run before =
      (fun reply => (reply, before)) <$> simulateQ effects (work.run sourceBefore) :=
  program_neutral _ (quiet sourceBefore) before

/-- Env suffixes preserve their actual role-installation count under the literal Word embedding. -/
theorem env_bound (role : Role) (work : OracleComp (EnvEffects n) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (InstallEnv role) cap) :
    (simulateQ (env (KemSK := KemSK)) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  by_cases installed : InstallEnv role query <;>
    simp [env, QueryImpl.apply_compose, effect, liftLocal, GlobalInstall,
      RegistrationNativeSecretWordAtomInstallCaps.Install, installed, isQueryBoundP_query_iff]

/-- The Env-only continuation cannot replace the descriptor established by its actual preceding demand. -/
theorem env_rootfree (work : OracleComp (EnvEffects n) A) :
    (simulateQ (env (KemSK := KemSK)) work).IsQueryBoundP (fun query => ¬ RootFree (KemSK := KemSK) query) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
  intro query
  simp [env, QueryImpl.apply_compose, effect, liftLocal, RootFree, isQueryBoundP_query_iff]

/-- The actual at-most-one Env installation suffix spends at most its current Word descriptor's atom credit. -/
theorem continuation (role : Role) (work : OracleComp (EnvEffects n) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (InstallEnv role) cap) (before : State) (result : A × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (env (KemSK := KemSK)) work)).run before)) :
    atom result.2.current ≤ atom before.current ∧ count role result.2 ≤ count role before + cap * atom before.current :=
  RegistrationNativeSecretWordAtomInstallTrace.program role _ cap (env_bound role work cap bounded) (env_rootfree work) before result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.embedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.query_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.query_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.program_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.program_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.state_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.state_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.env_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.env_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.env_rootfree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.env_rootfree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects.continuation
