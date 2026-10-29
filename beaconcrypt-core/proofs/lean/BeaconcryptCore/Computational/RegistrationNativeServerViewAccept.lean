-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSigningView

/-! The actual SDK accept wrapper preserves the original mandatory authentication, owned replay, reservation and one-use handle behavior under the explicit private analysis view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerViewAccept
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerMaterialSourceState (nativeView)
open RegistrationStateView (Stable)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- The complete Server view is idempotent and retains all public and private protocol control. -/
theorem view_idempotent (before : State n) : nativeView (nativeView before) = nativeView before := by
  simp only [nativeView, RegistrationNativeLocalView.project_idempotent]

/-- Actual post-authentication agreement retains every private consumed-ID branch and actual native reply. -/
theorem agree_input (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    Stable (nativeView (n := n)) (RegistrationServerNativeSource.agree setup checks representation created packet authenticated) := by
  intro before
  have law := congrArg (fun distribution => (fun result => (result.1,
    { nativeView before with world := result.2 })) <$> distribution)
    (RegistrationNativeLocalView.agreement_program setup.source
      (RegistrationServerRoleBackend.native setup checks representation created.seed)
      (RegistrationReplaySchedule.begin before.control authenticated before.consumed) before.world)
  simpa only [RegistrationServerNativeSource.agree, StateT.run, Functor.map_map,
    Prod.map, id_eq, nativeView, Function.comp_def] using law

/-- Retaining an accepted token uses exactly the actual consume result and append position. -/
theorem retain_input (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement) :
    Stable (nativeView (n := n)) (RegistrationServerNativeSource.retain created accepted) := by
  intro before
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore,
    StateT.run]
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div => simp only [nativeView, RegistrationServerFrontendCompiler.erase, consumed, map_pure, Prod.map, id_eq,
      RegistrationNativeLocalView.project_idempotent]
  | ok result =>
      rcases result with ⟨token, history⟩
      cases token <;> simp only [nativeView, RegistrationServerFrontendCompiler.erase, consumed, map_pure, Prod.map, id_eq,
        RegistrationNativeLocalView.project_idempotent]

/-- Replay and reservation failure retain the same complete reached authentication state. -/
theorem after_input (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    Stable (nativeView (n := n))
      (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated) := by
  intro before
  let next : RustM agreement.AgreementEffect → StateT (State n) ProbComp (RustM (Option Nat)) := fun completed =>
    match completed with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok (.ServerComplete accepted) => RegistrationServerNativeSource.retain created accepted
    | .ok _ => pure (.ok none)
  have runNext (completed : RustM agreement.AgreementEffect) (current : State n) :
      next completed current = match completed with
      | .fail error => pure (.fail error, current)
      | .div => pure (.div, current)
      | .ok (.ServerComplete accepted) => (RegistrationServerNativeSource.retain created accepted).run current
      | .ok _ => pure (.ok none, current) := by
    cases completed with
    | fail error | div => rfl
    | ok effect => cases effect <;> rfl
  have rest : ∀ completed, Stable (nativeView (n := n)) (next completed) := by
    intro completed
    cases completed with
    | fail error | div => exact RegistrationStateView.pure_stable _ view_idempotent _
    | ok effect => cases effect <;> first
        | exact RegistrationStateView.pure_stable _ view_idempotent _
        | exact retain_input created _
  have law := RegistrationStateView.bind_stable nativeView
    (RegistrationServerNativeSource.agree setup checks representation created packet authenticated) next
    (agree_input setup checks representation created packet authenticated) rest before
  by_cases replay : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [RegistrationServerSdkSource.afterAuthentication, StateT.run, nativeView, replay,
      ite_true, map_pure, Prod.map, id_eq, RegistrationNativeLocalView.project_idempotent]
  · by_cases reserved : checks.reserveRegistration = true
    · simp only [RegistrationServerSdkSource.afterAuthentication, StateT.run, nativeView,
        replay, reserved, Bool.false_eq_true, ite_false, ite_true, StateT.monad_bind_def, StateT.bind, runNext] at law ⊢
      exact law
    · simp only [RegistrationServerSdkSource.afterAuthentication, StateT.run, nativeView, replay,
        reserved, Bool.false_eq_true, ite_false, map_pure, Prod.map, id_eq, RegistrationNativeLocalView.project_idempotent]

/-- Whole mandatory-ML native SDK acceptance does not inspect omitted analysis counters or request-kind instrumentation. -/
theorem accept_input (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    Stable (nativeView (n := n))
      (RegistrationServerSdkSource.accept setup codec checks route verify representation created packet) := by
  unfold RegistrationServerSdkSource.accept
  apply RegistrationStateView.bind_stable
  · exact RegistrationNativeWorldViewAuthentication.native_auth_input setup codec route verify created packet
  · intro checked
    cases checked with
    | fail error | div => exact RegistrationStateView.pure_stable _ view_idempotent _
    | ok checked =>
        rcases checked with ⟨events, verdict⟩
        cases verdict <;> first
          | exact RegistrationStateView.pure_stable _ view_idempotent _
          | exact after_input setup checks representation created packet _

end BeaconcryptCore.Computational.RegistrationNativeServerViewAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.view_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.agree_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.agree_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.retain_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.retain_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.after_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.after_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.accept_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewAccept.accept_input
