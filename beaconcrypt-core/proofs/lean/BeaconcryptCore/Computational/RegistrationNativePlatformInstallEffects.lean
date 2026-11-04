-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
/-! Literal noninstalling source effects preserve the complete concrete G2 observer, including arbitrary allocator, signature and serialization outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePublicFrontend (Spec liftLocal effect)
open RegistrationNativeG2Trace (State handler)
open RegistrationNativePlatformPairedPublicationFree (Allowed Quiet)
variable {n : Nat} {KemSK S A : Type}

def env : QueryImpl (EnvEffects n) (OracleComp (Spec n KemSK)) := effect
def effects : QueryImpl (RegistrationNativePlatformEffectCompiler.Spec n) (OracleComp (Spec n KemSK))
  | .inl query => env query
  | .inr coin => env (.inl coin)

def embed : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n) (OracleComp (Spec n KemSK))
  | .inl message => (Spec n KemSK).query (.inl (.inr (.inl (.inl message))))
  | .inr query => effects query

/-- The effect projection is exactly the one used by the actual four-leaf source compiler. -/
theorem embedding : embed (n := n) (KemSK := KemSK) ∘ₛ RegistrationNativePlatformServerFrontendCompiler.embed = effects := by
  funext query
  cases query <;> simp only [QueryImpl.apply_compose,RegistrationNativePlatformServerFrontendCompiler.embed,
    simulateQ_spec_query,embed]

/-- Every allowed noninstalling actual source leaf retains the entire chronological G2 observer. -/
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
        simp only [effects, env, effect, liftLocal, simulateQ_spec_query,
          handler, StateT.run, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish]
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

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.embedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.query_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.query_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.program_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.program_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.state_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects.state_neutral
