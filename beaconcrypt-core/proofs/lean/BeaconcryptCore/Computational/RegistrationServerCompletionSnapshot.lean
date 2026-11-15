-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The actual Core completion derives its original allocation control on every branch. Successful pending candidates and failed completion results both retain that same snapshot; the SDK/native rollback agreement is therefore a source fact. -/
namespace BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot

theorem prepare (control : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (current : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (actual : pqxdh.server_prepare_commit control pending current availability = .ok (.Ok candidate)) :
    candidate.previous_state = control := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  cases next <;> cases availability
  all_goals simp only [pqxdh.server_prepare_commit, array_eq_abs, nextRun, bind_tc_ok] at actual
  all_goals split_ifs at actual <;> simp_all only [RustM.ok.injEq, core.result.Result.Ok.injEq, reduceCtorEq]
  all_goals cases actual; rfl

def Retains (control : pqxdh.ServerState) : core.result.Result registration.ServerAdHash pqxdh.ServerState → Prop
  | .Err previous => previous = control
  | .Ok pending => pending.candidate.previous_state = control

theorem ad_selection (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement) (application : Slice U8)
    (result : core.result.Result registration.ServerAdHash pqxdh.ServerState)
    (actual : registration.begin_server_completion control pin availability accepted application = .ok result) :
    Retains control result := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = .ok result := ⟨_, rfl⟩
  obtain ⟨matched, matchRun⟩ := BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total accepted.binding pin
  obtain ⟨prepared, prepareRun⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok control accepted.pending pin.binding availability
  cases prepared with
  | Err error =>
    cases empty <;> cases matched
    all_goals simp only [registration.begin_server_completion, emptyRun, matchRun, prepareRun,
      session.ServerAuthenticationPin.impl.binding, bind_tc_ok, ↓reduceIte, RustM.ok.injEq] at actual
    all_goals cases actual; rfl
  | Ok candidate =>
    obtain ⟨bytes, bytesRun, _⟩ := BeaconcryptCore.Refinement.RegistrationAd.pending_transcript_exact
      accepted.binding (BeaconcryptCore.Refinement.RegistrationAd.serverView candidate)
    simp only [BeaconcryptCore.Refinement.RegistrationAd.serverView] at bytesRun
    cases empty <;> cases matched
    all_goals simp only [registration.begin_server_completion, emptyRun, matchRun, prepareRun,
      session.ServerAuthenticationPin.impl.binding,
      pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key,
      pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key,
      pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext, pqxdh.ServerRegistrationCandidate.impl.key_id, bytesRun,
      bind_tc_ok, ↓reduceIte, RustM.ok.injEq] at actual
    all_goals cases actual
    all_goals first | rfl | exact prepare control accepted.pending pin.binding availability candidate prepareRun
end BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.ad_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.ad_selection
