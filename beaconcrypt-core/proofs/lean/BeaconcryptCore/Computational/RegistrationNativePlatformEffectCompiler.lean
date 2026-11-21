-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
/-! Public platform code and restricted World effects use distinct oracle branches. The compiler retains one public platform state and supplies no private World lens to public platform code. Its interpretation preserves the complete private Local and platform coordinates, with public random draws kept outside native counters. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler
open PqxdhRecordLiftInterface (EnvEffects)
variable {n : Nat} {Platform Auxiliary A B : Type}

abbrev Spec (n : Nat) := EnvEffects n + unifSpec

def publicCoin : QueryImpl unifSpec (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inr query)

def effect (query : (EnvEffects n).Domain) : StateT Platform (OracleComp (Spec n)) ((EnvEffects n).Range query) :=
  StateT.lift ((Spec n).query (.inl query) : OracleComp (Spec n) _)

def compile (work : StateT Platform ProbComp A) : StateT Platform (OracleComp (Spec n)) A :=
  fun previous => simulateQ publicCoin (work.run previous)

noncomputable def implementation : QueryImpl (Spec n) (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp)
  | .inl query => RegistrationServerPublicationWorldCompiler.effect query
  | .inr query => StateT.lift (unifSpec.query query : ProbComp _)

noncomputable def close (work : StateT Platform (OracleComp (Spec n)) A) :
    StateT (RegistrationWorldAgreement.State n Auxiliary) (StateT Platform ProbComp) A := fun current previous =>
  (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ implementation (work.run previous)).run current

private theorem lift_apply {S V : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (work : q V) (before : S) :
    (StateT.lift work : StateT S q V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Pure source work keeps the entire private and public state. -/
theorem close_pure (value : A) :
    close (Auxiliary := Auxiliary) (pure value : StateT Platform (OracleComp (Spec n)) A) = pure value := by
  funext current previous
  simp only [close, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

/-- Adaptive source continuations run on the same reached private and persistent public state. -/
theorem close_bind (work : StateT Platform (OracleComp (Spec n)) A)
    (next : A → StateT Platform (OracleComp (Spec n)) B) :
    close (Auxiliary := Auxiliary) (work >>= next) = (close work >>= fun value => close (next value)) := by
  funext current previous
  simp only [close, StateT.run, StateT.monad_bind_def, StateT.bind,
    simulateQ_bind, map_bind, bind_map_left]

private theorem external_program (work : ProbComp A) :
    simulateQ (implementation (n := n) (Auxiliary := Auxiliary)) (simulateQ publicCoin work) =
      StateT.lift work := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : implementation (n := n) (Auxiliary := Auxiliary) ∘ₛ publicCoin =
      (fun coin => StateT.lift (unifSpec.query coin : ProbComp _)) := by
    funext coin
    simp only [QueryImpl.apply_compose, publicCoin, simulateQ_spec_query, implementation]
  rw [leaves]
  exact simulateQ_liftTarget (QueryImpl.ofLift unifSpec ProbComp) work |>.trans
    (congrArg (fun action => (StateT.lift action : StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp A))
      (simulateQ_ofLift_eq_self work))

/-- Arbitrary effectful public code, including randomized retry tapes, retains its exact platform poststate and does not change private World or native counters. -/
theorem close_public (work : StateT Platform ProbComp A) :
    close (n := n) (Auxiliary := Auxiliary) (compile work) = StateT.lift work := by
  funext current previous
  simp only [close, compile, StateT.run, external_program, lift_apply, map_apply, Functor.map_map]
  rfl

private theorem native_program (work : ProbComp A) :
    simulateQ (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform)) work =
      StateT.lift work := by
  have coins : RegistrationNativePlatformMldsaProgram.coins (Platform := Platform) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Platform ProbComp) := rfl
  rw [coins, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  rfl

/-- Each restricted World request reaches the actual native World lens on the same full Local, while the public platform state remains external. -/
theorem close_effect (query : (EnvEffects n).Domain) :
    close (Auxiliary := Auxiliary) (effect (Platform := Platform) query) =
      RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins query := by
  funext current previous
  simp only [close, effect, StateT.run, lift_apply, map_apply,
    simulateQ_map, simulateQ_spec_query, implementation,
    RegistrationNativePlatformPairedServerService.nativeEffects, RegistrationNativePlatformServerCompletion.liftNative,
    native_program, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler.close_effect
