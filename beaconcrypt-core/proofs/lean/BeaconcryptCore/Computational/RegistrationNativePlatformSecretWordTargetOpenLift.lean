-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOpenRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase
/-! Purely algebraic lowering of the actual common-platform local leaves keeps all four mutable source coordinates. It exposes the unchanged local authentication and collector semantics without imposing a whole-controller equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift
open RegistrationNativePlatformSecretWordAtomOpenRun (State Base Work close Context)
variable {n : Nat} {KemSK Platform A B : Type}
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work :=
  bind_pure_comp _ _
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _
private theorem local_program (selected : Bool)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A) (previous : Platform) :
    (simulateQ (RegistrationNativePlatformSecretWordFrontendView.wordLocal selected) work) previous =
      (fun value => (value, previous)) <$> simulateQ (RegistrationNativeSecretWordInterface.liftLocal selected) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_apply,
      RegistrationNativePlatformSecretWordFrontendView.wordLocal, lift_apply,
      bind_map_left, ih, map_bind]

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (StateT (Context n KemSK) ProbComp))
/-- A local free leaf program keeps the exact platform object and lowers to its literal environment/private interpreter. -/
theorem local_run (selected : Bool)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A) (before : State n KemSK Platform) :
    (close implementation (StateT.lift (StateT.lift
      (simulateQ (RegistrationNativePlatformSecretWordFrontendView.wordLocal selected) work)))).run before =
      (fun result => (result.1,(before.1,(result.2.1,(before.2.2.1,result.2.2))))) <$>
        (RegistrationNativeSecretWordTargetServerExecution.lower
          (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal selected)
          (StateT.lift work)).run (before.2.1,before.2.2.2) := by
  rw [RegistrationNativeSecretWordTargetServerExecution.lower_run]
  simp only [close,StateT.run,lift_apply,local_program,simulateQ_map,map_apply,
    QueryImpl.simulateQ_compose,Functor.map_map]
  rfl

/-- The exact effectful environment source, including mandatory authentication hashes, has the same local lowering. -/
theorem environment_run (selected : Bool) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (before : State n KemSK Platform) :
    (close implementation (StateT.lift (StateT.lift
      (simulateQ (RegistrationNativePlatformSecretWordOpen.effects
        (RegistrationNativePlatformSecretWordFrontendView.wordLocal selected)) work)))).run before =
      (fun result => (result.1,(before.1,(result.2.1,(before.2.2.1,result.2.2))))) <$>
        (RegistrationNativeSecretWordTargetServerExecution.lower
          (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal selected)
          (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect work))).run
            (before.2.1,before.2.2.2) := by
  rw [RegistrationNativePlatformSecretWordOpen.effects,QueryImpl.simulateQ_compose]
  exact local_run implementation selected _ before

/-- A common-base computation retains the local Server and source environment while threading the exact platform/private result. -/
theorem lifted_run (work : Base n KemSK Platform A) (before : State n KemSK Platform) :
    (close implementation (StateT.lift (StateT.lift work))).run before =
      (fun result => (result.1.1,(before.1,(before.2.1,(result.1.2,result.2))))) <$>
        (simulateQ implementation (work.run before.2.2.1)).run before.2.2.2 := by
  simp only [close,StateT.run,lift_apply,map_apply,simulateQ_map,Functor.map_map]
  rfl

/-- Mapping a common-base reply changes no coordinate of its actual poststate. -/
theorem lifted_map (work : Base n KemSK Platform A) (observe : A → B) (before : State n KemSK Platform) :
    (close implementation (StateT.lift (StateT.lift (observe <$> work)))).run before =
      Prod.map observe id <$> (close implementation (StateT.lift (StateT.lift work))).run before := by
  simp only [close,StateT.run,lift_apply,map_apply,simulateQ_map,Functor.map_map]
  rfl

/-- Repeated fingerprint computation is its literal one environment hash with the actual returned digest. -/
theorem pin {m : Type → Type} [Monad m] [LawfulMonad m]
    (effects : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m) (current : session.ServerAuthenticationPin) :
    RegistrationNativePlatformServerReferenceAccept.pin effects current =
      (fun digest => .ok (.Some (⟨current.binding,current.public_key,
        RegistrationAuthenticationShared.digestArray digest⟩ : session.ServerAuthenticationPin))) <$>
        effects (.inr (.hash (PqxdhRefinement.absBytes current.public_key))) := by
  simp only [RegistrationNativePlatformServerReferenceAccept.pin,RegistrationNativeServerPinRecompute.program,
    RegistrationNativePlatformServerReferenceAccept.hash,simulateQ_map,simulateQ_spec_query,Functor.map_map,
    bind_pure_comp,RegistrationNativeServerPinRecompute.request,
    BeaconcryptCore.Refinement.RegistrationInputs.hashBytes,Std.Array.to_slice]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.local_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.environment_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.environment_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.lifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.lifted_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.lifted_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.lifted_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift.pin
