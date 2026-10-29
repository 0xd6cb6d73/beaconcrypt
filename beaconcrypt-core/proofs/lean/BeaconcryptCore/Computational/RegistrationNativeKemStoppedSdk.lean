-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter

/-! The actual SDK cannot return a successful session before its selected literal KEM getter. Authentication, replay/reservation checks, source request logging and parsed-attempt mutation all remain in their original positions. The final cut consequence is derived from actual source syntax, not assumed as a session/mark correspondence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemNoInput (NoSome prefix_no_some optional_no_some)
open RegistrationNativeKemStoppedGetter (node serverResult)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def lower : QueryImpl (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
    (OptionT (OracleComp (Spec n mlSource KemSK))) :=
  (RegistrationNativeKemStoppedGetter.stop ∘ₛ RegistrationNativeKemRouting.route true) ∘ₛ
    RegistrationNativeKemFrontendInterface.lift

private theorem lower_program
    (work : OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) Value) :
    simulateQ lower work = simulateQ RegistrationNativeKemStoppedGetter.stop
      (simulateQ (RegistrationNativeKemRouting.route true) (simulateQ RegistrationNativeKemFrontendInterface.lift work)) := by
  simp only [lower, QueryImpl.simulateQ_compose]

private theorem agreement_program (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    simulateQ lower (simulateQ (RegistrationNativeKemServerInterface.agreement (n := n) (mlSource := mlSource) setup checks) work) =
      simulateQ (node setup checks) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact lower_program _

def sessionResult : RustM (Option Nat) → Option Nat
  | .ok value => value
  | _ => none

private theorem pure_none {Result : Type} : NoSome (pure none : OptionT (OracleComp (Spec n mlSource KemSK)) (Option Result)) := by
  intro value
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq, reduceCtorEq, not_false_eq_true]

private def continuation (result : RustM agreement.AgreementEffect) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.ServerComplete accepted) => (RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.retain accepted))
  | .ok _ => pure (.ok none)

private def retained (accepted : Option agreement.ServerAgreement) :
    OptionT (OracleComp (Spec n mlSource KemSK)) (Option Nat) :=
  match accepted with
  | none => pure none
  | some accepted => sessionResult <$> simulateQ lower
      ((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.retain accepted)) :
        OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)))

private theorem continuation_eq (result : RustM agreement.AgreementEffect) :
    sessionResult <$> simulateQ (lower (n := n) (mlSource := mlSource) (KemSK := KemSK)) (continuation result) =
      retained (serverResult result) := by
  cases result with
  | fail error | div => simp only [continuation, simulateQ_pure, map_pure, sessionResult, serverResult, retained]
  | ok effect => cases effect <;>
      simp only [continuation, simulateQ_pure, map_pure, sessionResult, serverResult, retained]

private theorem after_no_session (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    NoSome (sessionResult <$> simulateQ (lower (n := n) (mlSource := mlSource))
      (RegistrationNativeKemSdkCompiler.afterAuthentication setup checks authenticated)) := by
  simp only [RegistrationNativeKemSdkCompiler.afterAuthentication, simulateQ_bind, map_bind]
  apply prefix_no_some
  intro before
  split
  · simpa only [simulateQ_pure, map_pure, sessionResult] using
      (pure_none (n := n) (mlSource := mlSource) (KemSK := KemSK))
  · split
    · simp only [simulateQ_bind, agreement_program, map_bind]
      change NoSome (simulateQ (node setup checks)
        (RegistrationReplaySchedule.begin before.server.control authenticated before.server.consumed) >>=
          fun result => sessionResult <$> simulateQ lower (continuation result))
      simp_rw [continuation_eq]
      have stopped := optional_no_some _
        (RegistrationNativeKemStoppedGetter.agreement_no_completion (n := n) (mlSource := mlSource)
          setup checks before.server.control packet authenticated before.server.consumed)
        retained (pure_none (n := n) (mlSource := mlSource) (KemSK := KemSK))
      simpa only [bind_map_left] using stopped
    · simpa only [simulateQ_pure, map_pure, sessionResult] using
        (pure_none (n := n) (mlSource := mlSource) (KemSK := KemSK))

/-- Every literal SDK authentication/replay/reservation branch fails to issue a successful session if the selected getter is stopped. -/
theorem accept_no_session (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) :
    NoSome (sessionResult <$> simulateQ (lower (n := n) (mlSource := mlSource))
      (RegistrationNativeKemServerInterface.accept setup checks packet)) := by
  simp only [RegistrationNativeKemServerInterface.accept, simulateQ_bind, map_bind]
  apply prefix_no_some
  intro checked
  cases checked with
  | fail error | div => simpa only [simulateQ_pure, map_pure, sessionResult] using
      (pure_none (n := n) (mlSource := mlSource) (KemSK := KemSK))
  | ok result =>
      rcases result with ⟨events, result⟩
      cases result with
      | Accepted authenticated => exact after_no_session setup checks packet authenticated
      | _ => simpa only [simulateQ_pure, map_pure, sessionResult] using
          (pure_none (n := n) (mlSource := mlSource) (KemSK := KemSK))

/-- Parsed-attempt mutation precedes the same actual SDK path and cannot manufacture a completed session before encapsulation. -/
theorem typed_no_session (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) :
    NoSome (sessionResult <$> simulateQ (lower (n := n) (mlSource := mlSource))
      (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) := by
  simp only [RegistrationNativeKemServerInterface.typedAccept, simulateQ_bind, map_bind]
  exact prefix_no_some _ _ (fun _ => accept_no_session setup checks packet)

/-- Any actual stateful interpretation of the chosen native typed accept must suspend at the first selected getter before it can produce a successful session. -/
theorem completed_accept_impossible {S : Type}
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (implementation : QueryImpl (Spec n mlSource KemSK) (StateT S ProbComp))
    (session : Nat) (before after : S)
    (supported : (RegistrationNativeKemCut.Cut.complete (.ok (some session)), after) ∈ support
      ((RegistrationNativeKemCut.scan implementation
        (simulateQ (RegistrationNativeKemRouting.route true) (simulateQ RegistrationNativeKemFrontendInterface.lift
          (RegistrationNativeKemServerInterface.typedAccept setup checks packet))) 0).run before)) : False := by
  have original := RegistrationNativeKemCutStop.completed_support implementation _ (.ok (some session) : RustM (Option Nat)) before after supported
  have stopped : some (.ok (some session)) ∈ support
      ((simulateQ (lower (n := n) (mlSource := mlSource))
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet)).run) := by
    simpa only [lower_program, RegistrationNativeKemStoppedGetter.stop] using original
  apply typed_no_session (n := n) (mlSource := mlSource) setup checks packet session
  rw [OptionT.run_map, support_map]
  exact Set.mem_image_of_mem (Option.map sessionResult) stopped

end BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk.accept_no_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk.accept_no_session
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk.typed_no_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk.typed_no_session
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk.completed_accept_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk.completed_accept_impossible
