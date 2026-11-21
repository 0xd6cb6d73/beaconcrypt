-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService
/-! Exact neutral footprint of real hash, primitive and independent-coin leaves for opaque slot instrumentation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift coinLift)
open RegistrationNativePlatformRecordSlotGhost (State next handler program)
variable {n : Nat} {A : Type}

def Quiet : (WorldSpec n).Domain → Prop
  | .inr (.inl (.inr (.installServer _ _ _))) => False
  | .inr (.inl (.inr (.installBeacon _ _ _))) => False
  | .inr (.inl (.inr (.appendOwner _ _ _))) => False
  | _ => True

def EffectQuiet : (EnvEffects n).Domain → Prop
  | .inr (.installServer _ _ _) => False
  | .inr (.installBeacon _ _ _) => False
  | .inr (.appendOwner _ _ _) => False
  | _ => True

/-- Every non-installation, non-allocation request leaves the complete opaque slot receipt unchanged, for every reply. -/
theorem next_quiet (query : (WorldSpec n).Domain) (quiet : Quiet query)
    (reply : (WorldSpec n).Range query) (before : State n) : next query reply before=before := by
  rcases query with coin | ((coin | capability) | record)
  · rfl
  · rfl
  · cases capability <;> first | contradiction | rfl
  · cases record <;> rfl

/-- Neutral source trees forward all replies and preserve the entire slot observer without adding queries. -/
theorem program_quiet (work : OracleComp (WorldSpec n) A) (quiet : work.AllQueriesSatisfy Quiet) (before : State n) :
    program work before=(fun value => (value,before)) <$> work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [program,simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query continuation ih =>
    rw [program,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    simp only [handler,StateT.run,bind_map_left,map_bind]
    apply bind_congr
    intro reply
    rw [next_quiet query quiet.1 reply before]
    exact ih reply (quiet.2 reply) before

private theorem every {I : Type} {spec : OracleSpec I} (work : OracleComp spec A) : work.AllQueriesSatisfy (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query continuation ih => exact ⟨trivial,ih⟩

/-- Arbitrary independent probabilistic computations expose coins only and cannot modify slot provenance. -/
theorem coins_quiet (work : ProbComp A) : (simulateQ (coinLift (n := n)) work).AllQueriesSatisfy Quiet := by
  apply RegistrationNativeHiddenAllocationCore.simulation _ (fun _ => True) Quiet _ work (every work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

/-- Lifting actual neutral environment effects into the shared World retains the same slot footprint. -/
theorem effects_quiet (work : OracleComp (EnvEffects n) A) (quiet : work.AllQueriesSatisfy EffectQuiet) :
    (simulateQ effectLift work).AllQueriesSatisfy Quiet := by
  apply RegistrationNativeHiddenAllocationCore.simulation effectLift EffectQuiet Quiet _ work quiet
  intro query permitted
  apply (allQueriesSatisfy_query_iff _ _).mpr
  rcases query with coin | capability
  · trivial
  · cases capability <;> exact permitted

private theorem three {I : Type} {spec : OracleSpec I} (work : OracleComp spec A) (p q r s : I → Prop)
    (left : work.AllQueriesSatisfy p) (middle : work.AllQueriesSatisfy q) (right : work.AllQueriesSatisfy r)
    (implies : ∀query,p query → q query → r query → s query) : work.AllQueriesSatisfy s := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query continuation ih =>
    exact ⟨implies query left.1 middle.1 right.1, fun reply => ih reply (left.2 reply) (middle.2 reply) (right.2 reply)⟩

/-- Native publication compilation has no installation or allocation leaf, including all ML signer and record failures. -/
theorem publication_quiet (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : List RegistrationSigningShared.Receipt) :
    ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run before).AllQueriesSatisfy EffectQuiet := by
  have noAppend := RegistrationNativeHiddenAllocationService.publication (n := n) source writer sign query before
  have server := RegistrationNativeSecretWordAtomInstallCompiler.publication_free (n := n) .server source writer sign query before
  have beacon := RegistrationNativeSecretWordAtomInstallCompiler.publication_free (n := n) .beacon source writer sign query before
  have server' : ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run before).AllQueriesSatisfy
      (fun query => ¬RegistrationNativeSecretWordAtomInstallCaps.InstallEnv .server query) := by
    apply (isQueryBoundP_zero_iff _ (fun query => ¬RegistrationNativeSecretWordAtomInstallCaps.InstallEnv .server query)).mp
    simpa only [not_not] using server
  have beacon' : ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run before).AllQueriesSatisfy
      (fun query => ¬RegistrationNativeSecretWordAtomInstallCaps.InstallEnv .beacon query) := by
    apply (isQueryBoundP_zero_iff _ (fun query => ¬RegistrationNativeSecretWordAtomInstallCaps.InstallEnv .beacon query)).mp
    simpa only [not_not] using beacon
  apply three _ _ _ _ EffectQuiet noAppend server' beacon'
  intro query allocation server beacon
  rcases query with coin | capability
  · trivial
  · cases capability <;> first | exact server rfl | exact beacon rfl | exact Nat.noConfusion allocation | trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.next_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.next_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.program_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.program_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.coins_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.coins_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.effects_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.effects_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.publication_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral.publication_quiet
