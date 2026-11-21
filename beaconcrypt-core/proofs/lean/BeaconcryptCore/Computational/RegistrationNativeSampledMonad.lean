-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSampling

/-! Literal native sampling is a monadic interpretation of ordinary probabilistic computation. These exact laws retain the complete original World and actual underlying uniform query count. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSampledMonad
open PqxdhRecordLiftWorld (sampled)
variable {n : Nat} {X Y : Type}

/-- Pure native sampling has no hidden draw or World effect. -/
theorem pure (value : X) (before : PqxdhRecordLiftWorld.State n) :
    (sampled (Pure.pure value : ProbComp X)).run before = Pure.pure (value, before) := by
  simp only [sampled, StateT.run, simulateQ_pure, ]
  rfl

/-- Splitting a native probabilistic bind keeps the exact source World and accumulated uniform count. -/
theorem bind (first : ProbComp X) (next : X → ProbComp Y) (before : PqxdhRecordLiftWorld.State n) :
    (sampled (first >>= next)).run before = (do
      let initial ← (sampled first).run before
      (sampled (next initial.1)).run initial.2) := by
  simp only [sampled, StateT.run, simulateQ_bind, StateT.monad_bind_def, StateT.bind,
    bind_assoc, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeSampledMonad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSampledMonad.pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSampledMonad.pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSampledMonad.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSampledMonad.bind
