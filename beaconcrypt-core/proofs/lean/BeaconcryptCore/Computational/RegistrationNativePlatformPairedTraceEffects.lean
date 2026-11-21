-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree
import BeaconcryptCore.Computational.RegistrationNativePairedCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
/-! Actual noninstalling Env effects and external coins preserve the complete paired observer. A literal material demand records its actual reply and descriptor before any fixed-slot continuation. This analysis algebra retains every original query/reply and mutable source result; it makes no alias-exclusion or security claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePairedTrace (State handler step Fits Safe)
open RegistrationNativePlatformPairedPublicationFree (Allowed Quiet)
variable {n : Nat} {KemSK S A B : Type}

def effects : QueryImpl (RegistrationNativePlatformEffectCompiler.Spec n) (OracleComp (Spec n KemSK))
  | .inl query => RegistrationNativePairedCompile.effects query
  | .inr coin => RegistrationNativePairedCompile.effects (.inl coin)

def demand (message : RegistrationNativeRelatedFamily.Message) :
    OracleComp (Spec n KemSK) (Option (RegistrationNativePairedChoice.Choice n)) :=
  (Spec n KemSK).query (.inl (.inr (.inl (.inl message))))

theorem query_neutral (query : (RegistrationNativePlatformEffectCompiler.Spec n).Domain)
    (allowed : Allowed query) (before : State n) :
    (simulateQ handler (effects (KemSK := KemSK) query)).run before =
      (fun reply => (reply, before)) <$> effects query := by
  cases query with
  | inl query =>
    have exactRun := RegistrationNativePairedCompile.effects_source (KemSK := KemSK)
        (((PqxdhRecordLiftInterface.EnvEffects n).query query) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _)
        (fun role => by
          rw [isQueryBoundP_query_iff]
          intro installed
          exact (allowed role installed).elim) before
    simp only [simulateQ_spec_query] at exactRun
    convert exactRun using 1 <;> rfl
  | inr coin =>
    have exactRun := RegistrationNativePairedCompile.effects_source (KemSK := KemSK)
        (((PqxdhRecordLiftInterface.EnvEffects n).query (.inl coin)) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _)
        (fun role => by simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]) before
    simp only [simulateQ_spec_query] at exactRun
    convert exactRun using 1 <;> rfl

theorem program_neutral (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A)
    (allowed : work.AllQueriesSatisfy Allowed) (before : State n) :
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

/-- Literal stateful source publication retains its full returned state while leaving every paired-observer field unchanged. -/
theorem state_neutral (work : StateT S (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : Quiet work) (sourceBefore : S) (before : State n) :
    (simulateQ handler (simulateQ (effects (KemSK := KemSK)) (work.run sourceBefore))).run before =
      (fun reply => (reply, before)) <$> simulateQ effects (work.run sourceBefore) :=
  program_neutral _ (quiet sourceBefore) before

theorem program_safe (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A)
    (allowed : work.AllQueriesSatisfy Allowed) : Safe (simulateQ (effects (KemSK := KemSK)) work) := by
  intro before result clean supported
  rw [program_neutral work allowed before] at supported
  rw [support_map] at supported
  rcases supported with ⟨reply, _, rfl⟩
  exact clean

/-- The actual material request preserves cleanliness and stores exactly its returned choice and demanded descriptor. -/
theorem demand_step (message : RegistrationNativeRelatedFamily.Message)
    (reply : Option (RegistrationNativePairedChoice.Choice n)) (before : State n) :
    (step (KemSK := KemSK) (.inl (.inr (.inl (.inl message)))) reply before).bad = before.bad ∧
    (step (KemSK := KemSK) (.inl (.inr (.inl (.inl message)))) reply before).trace.current = some message ∧
    (step (KemSK := KemSK) (.inl (.inr (.inl (.inl message)))) reply before).choice = reply := by
  simp [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
    RegistrationNativePairedTrace.updateChoice, Fits]

theorem fits_hidden (reference : RegistrationNativePairedDemand.Reference n) (before : State n)
    (current : before.trace.current.isSome = true) (chosen : before.choice = some (.hidden reference)) :
    RegistrationNativePairedTrace.FitsKernel before (.hidden reference.slot) :=
  ⟨current, reference, chosen, rfl⟩

theorem clean_step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (before : State n) (valid : Fits query before) : (step query reply before).bad = before.bad := by
  simp only [step, valid, decide_true, Bool.not_true, Bool.or_false]

/-- A stateful free source program whose every reached leaf is safe composes with its exact returned state and all adaptive replies. -/
theorem state_program_safe {I : Type} {queries : OracleSpec I}
    (implementation : QueryImpl queries (StateT S (OracleComp (Spec n KemSK))))
    (leaf : ∀ query before, Safe ((implementation query).run before))
    (work : OracleComp queries A) (before : S) : Safe ((simulateQ implementation work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact RegistrationNativePairedTrace.pure_safe _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact RegistrationNativePairedTrace.bind_safe _ _ (leaf query before) (fun result => ih result.1 result.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.query_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.query_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.program_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.program_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.state_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.state_neutral

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.program_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.demand_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.demand_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.fits_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.fits_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.clean_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.clean_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.state_program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects.state_program_safe
