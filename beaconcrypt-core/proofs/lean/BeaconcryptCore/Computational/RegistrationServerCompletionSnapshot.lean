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
  obtain ⟨ad, adRun⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok current.identity_public_key pending.beacon_identity_public_key
  cases next <;> cases availability
  all_goals simp only [pqxdh.server_prepare_commit, array_eq_abs, nextRun, adRun, bind_tc_ok] at actual
  all_goals split_ifs at actual <;> simp_all only [RustM.ok.injEq, core.result.Result.Ok.injEq, reduceCtorEq]
  all_goals cases actual; rfl

def Retains (control : pqxdh.ServerState) : core.result.Result registration.ServerInitialKdf pqxdh.ServerState → Prop
  | .Err previous => previous = control
  | .Ok pending => pending.candidate.previous_state = control

theorem initial (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (accepted : agreement.ServerAgreement) (application : Slice U8)
    (result : core.result.Result registration.ServerInitialKdf pqxdh.ServerState)
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
    obtain ⟨pending, pendingRun⟩ := BeaconcryptCore.PanicFreedom.Structural.pqxdh_concrete_start_server_candidate_ratchet_kdf_total candidate accepted.root.bytes
    cases empty <;> cases matched
    all_goals simp only [registration.begin_server_completion, emptyRun, matchRun, prepareRun,
      session.ServerAuthenticationPin.impl.binding, ratchet.RatchetChain.as_bytes, pendingRun,
      bind_tc_ok, ↓reduceIte, RustM.ok.injEq] at actual
    all_goals cases actual
    all_goals first | rfl | exact prepare control accepted.pending pin.binding availability candidate prepareRun
end BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot.initial
