-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure
/-! Trusted source child programs lift through a private signing-cut state without inspecting or changing that cut. Pure, bind and every adaptive oracle continuation commute with the lift, retaining the complete native and base-monad state. This composes actual child writer programs rather than introducing a whole writer correspondence premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCutLift
open RegistrationNativePlatformCutErasure (liftWorld)
open RegistrationNativePlatformCutJournal (State)
variable {S A B I : Type} {queries : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem pure_lifted (value : A) :
    liftWorld (pure value : StateT S m A) = (pure value : StateT (State S) m A) := by
  funext before
  change (fun result : A × S => (result.1, (result.2, before.2))) <$>
    (pure (value, before.1) : m (A × S)) = pure (value, before)
  simp only [map_pure]

theorem bind_lifted (work : StateT S m A) (next : A → StateT S m B) :
    liftWorld (work >>= next) = (do let value ← liftWorld work; liftWorld (next value)) := by
  funext before
  change (fun result : B × S => (result.1, (result.2, before.2))) <$>
    (work.run before.1 >>= fun result => (next result.1).run result.2) =
    ((fun result : A × S => (result.1, (result.2, before.2))) <$> work.run before.1 >>= fun result =>
      (fun last : B × S => (last.1, (last.2, result.2.2))) <$> (next result.1).run result.2.1)
  simp only [map_bind, bind_map_left]

theorem program (impl : QueryImpl queries (StateT S m)) (work : OracleComp queries A) :
    simulateQ (fun query => liftWorld (impl query)) work = liftWorld (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using (pure_lifted (S := S) (m := m) value).symm
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_lifted]
      apply bind_congr
      intro reply
      exact ih reply
end BeaconcryptCore.Computational.RegistrationNativePlatformCutLift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutLift.pure_lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutLift.pure_lifted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutLift.bind_lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutLift.bind_lifted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutLift.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutLift.program
