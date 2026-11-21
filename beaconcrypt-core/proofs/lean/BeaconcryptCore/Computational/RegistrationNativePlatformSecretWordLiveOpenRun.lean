-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer
/-! The corrected symbolic Server controller is interpreted once over its actual Server, environment, platform and preparation states. Algebraic closure preserves every reached reserve result and all interpreter effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun
open RegistrationNativeSecretWordMessage (ServerState)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Platform A B : Type}
abbrev Context (n : Nat) (KemSK : Type) := RegistrationNativeSecretWordInterpreter.State n KemSK
abbrev State (n : Nat) (KemSK Platform : Type) := ServerState × (Environment × (Platform × Context n KemSK))
abbrev Base (n : Nat) (KemSK Platform : Type) := StateT Platform (OracleComp (Spec n KemSK))
abbrev Work (n : Nat) (KemSK Platform : Type) := RegistrationNativePlatformSecretWordOpen.PublicM (Base n KemSK Platform)

def close (implementation : QueryImpl (Spec n KemSK) (RegistrationNativeSecretWordInterpreter.M n KemSK))
    (work : Work n KemSK Platform A) : StateT (State n KemSK Platform) RegistrationNativeSecretWordLiveServerRun.Target A := fun before =>
  (fun result => (result.1.1.1.1, (result.1.1.1.2, (result.1.1.2, (result.1.2, result.2))))) <$>
    (simulateQ implementation (((work.run before.1).run before.2.1).run before.2.2.1)).run before.2.2.2

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work :=
  bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before, before) := rfl

variable (implementation : QueryImpl (Spec n KemSK) (RegistrationNativeSecretWordInterpreter.M n KemSK))

/-- Pure controller returns preserve the complete four-state execution. -/
theorem pure_run (value : A) (before : State n KemSK Platform) :
    (close implementation (pure value)).run before = pure (value, before) := by
  simp only [close, StateT.run, pure_apply, simulateQ_pure, map_pure]

/-- Reading the current Server does not change any platform or preparation state. -/
theorem get_run (before : State n KemSK Platform) :
    (close implementation get).run before = pure (before.1, before) := by
  simp only [close, StateT.run, get_apply, pure_apply, simulateQ_pure, map_pure]

/-- The actual nested controller bind uses the same reached common state in its continuation. -/
theorem bind_run (work : Work n KemSK Platform A) (next : A → Work n KemSK Platform B)
    (before : State n KemSK Platform) :
    (close implementation (work >>= next)).run before = (do
      let result ← (close implementation work).run before
      (close implementation (next result.1)).run result.2) := by
  simp only [close, StateT.run, bind_apply, simulateQ_bind, bind_map_left, map_bind]

/-- Every computation lifted from the common platform monad retains the whole local Server. -/
theorem lifted_server (work : Base n KemSK Platform A) (before : State n KemSK Platform)
    (result : A × State n KemSK Platform)
    (supported : result ∈ support ((close implementation (StateT.lift (StateT.lift work))).run before)) :
    result.2.1 = before.1 := by
  simp only [close, StateT.run, lift_apply, map_apply, simulateQ_map, Functor.map_map, support_map] at supported
  obtain ⟨reached, _possible, equal⟩ := supported
  exact (congrArg (fun value => value.2.1) equal).symm

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

/-- The unchanged indexed collector and preparation run with the same live platform state. -/
theorem agreement_run {I : Type} {base : OracleSpec I}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (selected : Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Platform) :
    (close implementation (RegistrationNativePlatformSecretWordOpen.agreement
      (RegistrationNativePlatformSecretWordFrontendView.wordLocal selected) setup checks packet authenticated)).run before =
      (fun result => (result.1, (result.2.1, (result.2.2.1, (before.2.2.1, result.2.2.2))))) <$>
        (RegistrationNativeSecretWordLiveServerRun.close
          (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal selected)
          (RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated)).run
          (before.1, (before.2.1, before.2.2.2)) := by
  rw [RegistrationNativeSecretWordLiveServerRun.close_program]
  simp only [close, RegistrationNativePlatformSecretWordOpen.agreement, StateT.run, local_program,
    simulateQ_map, map_apply, QueryImpl.simulateQ_compose, Functor.map_map]
  rfl

/-- Actual one-use retention runs on the supplied common state and changes no preparation flag. -/
theorem retain_run (ready : RegistrationNativeSecretWordMessage.ServerReady) (before : State n KemSK Platform) :
    (close implementation (RegistrationNativePlatformSecretWordOpen.retain ready)).run before =
      match RegistrationNativeSecretWordServerMaterial.retain ready before.1 with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok (reply, after) => pure (.ok reply, (after, before.2)) := by
  cases kept : RegistrationNativeSecretWordServerMaterial.retain ready before.1 <;>
    simp only [close, RegistrationNativePlatformSecretWordOpen.retain, kept, StateT.run,
      pure_apply, simulateQ_pure, map_pure]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun






/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.pure_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.pure_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.get_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.get_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.bind_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.bind_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.lifted_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.lifted_server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.agreement_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.agreement_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.retain_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpenRun.retain_run
