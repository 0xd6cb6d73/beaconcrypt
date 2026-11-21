-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderLocal

/-! The actual open Server accept controller lowers through the same provider callbacks on its current environment. Native authentication precedes replay and reservation; optional agreement results precede one-use retention. These algebraic source equations retain every reached state on failure and introduce no callback-security premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderLocal (lower)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev Auxiliary (n : Nat) (KemSK ProviderState : Type) := RegistrationServerReferenceCompiler.Environment ×
  RegistrationNativeProviderInterpreter.State n KemSK ProviderState
abbrev State (n : Nat) (KemSK ProviderState : Type) := RegistrationServerMaterialFrontend.State × Auxiliary n KemSK ProviderState

def close (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp))
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) : StateT (State n KemSK ProviderState) ProbComp Value :=
  fun before => (fun result => (result.1.1, (result.1.2, result.2))) <$> (lower implementation (work.run before.1)).run before.2

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (state : S) : (get : StateT S m S) state = pure (state, state) := rfl

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun result => pure (result, state)) = _
  rw [bind_pure_comp]

variable (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
  (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp))

theorem close_pure (value : Value) (before : State n KemSK ProviderState) :
    (close implementation (pure value)).run before = pure (value, before) := by
  simp only [close, lower, StateT.run, state_pure_apply, simulateQ_pure, map_pure]

theorem close_get (before : State n KemSK ProviderState) :
    (close implementation get).run before = pure (before.1, before) := by
  simp only [close, lower, StateT.run, state_get_apply, state_pure_apply, simulateQ_pure, map_pure]

theorem close_bind {Result : Type} (first : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (next : Value → RegistrationServerOpenReferenceCompiler.M n KemSK Result) (before : State n KemSK ProviderState) :
    (close implementation (first >>= next)).run before = (do
      let result ← (close implementation first).run before
      (close implementation (next result.1)).run result.2) := by
  simp only [close, lower, StateT.run, state_bind_apply, simulateQ_bind, bind_map_left, map_bind, Functor.map_map]

theorem retain_run (ready : RegistrationServerReferenceRoot.Ready) (before : State n KemSK ProviderState) :
    (close implementation (RegistrationServerOpenReferenceCompiler.retain ready)).run before =
      match RegistrationServerMaterialFrontend.retain ready before.1 with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok (reply, after) => pure (.ok reply, (after, before.2)) := by
  cases retained : RegistrationServerMaterialFrontend.retain ready before.1 <;>
    simp only [close, lower, RegistrationServerOpenReferenceCompiler.retain, retained,
      StateT.run, state_pure_apply, simulateQ_pure, map_pure]

theorem agreement_run (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK ProviderState) :
    (close implementation (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before = (do
      let collected ← (lower implementation (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)).run before.2
      match collected.1 with
      | none => pure (.ok none, (before.1, collected.2))
      | some input =>
          (fun result => (result.1, (before.1, (collected.2.1, result.2)))) <$>
            (simulateQ implementation (simulateQ RegistrationBeaconReferenceCompiler.prepare
              (RegistrationServerReferenceRoot.client authenticated.binding input))).run collected.2.2) := by
  simp only [close, RegistrationServerOpenReferenceCompiler.agreement, lower, StateT.run,
    state_bind_apply, state_lift_apply, state_map_apply, simulateQ_bind, bind_map_left, map_bind, Functor.map_map]
  apply bind_congr
  rintro ⟨⟨input, env⟩, current⟩
  cases input <;> simp only [simulateQ_pure, simulateQ_map, state_pure_apply, state_map_apply,
    state_lift_apply, map_pure, Functor.map_map, Prod.map_def, id_eq]

theorem after_run (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK ProviderState) :
    (close implementation (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before =
      (if before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
      else if checks.reserveRegistration then do
        let completed ← (close implementation (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before
        match completed.1 with
        | .fail error => pure (.fail error, completed.2)
        | .div => pure (.div, completed.2)
        | .ok none => pure (.ok none, completed.2)
        | .ok (some ready) => (close implementation (RegistrationServerOpenReferenceCompiler.retain ready)).run completed.2
      else pure (.ok none, before)) := by
  rw [RegistrationServerOpenReferenceCompiler.afterAuthentication, close_bind, close_get, pure_bind]
  split
  · exact close_pure implementation (RustM.ok (none : Option Nat)) before
  · split
    · rw [close_bind]
      apply bind_congr
      rintro ⟨accepted, current⟩
      cases accepted with
      | fail error => exact close_pure implementation (RustM.fail error) current
      | div => exact close_pure implementation (RustM.div : RustM (Option Nat)) current
      | ok accepted => cases accepted with
        | none => exact close_pure implementation (RustM.ok (none : Option Nat)) current
        | some ready => rfl
    · exact close_pure implementation (RustM.ok (none : Option Nat)) before

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.close_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.close_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.close_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.close_get
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.close_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.close_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.retain_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.retain_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.agreement_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.agreement_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.after_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun.after_run
