-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementExecutor
import BeaconcryptCore.Refinement.PeerOwnership

/-! Replay status belongs to a persistent private registration-ID set, rather than an adversarial Fresh argument. Both membership and insertion use the actual native ownership capabilities. Source insertion occurs after completed root agreement and before response completion; the later callback receives no set lens, so signing/encoding/publication failure cannot undo consumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationReplaySchedule

abbrev State := List Pqxdh.Bytes

def identifier (authenticated : registration.AuthenticatedInit) : Pqxdh.Bytes :=
  (absVerified authenticated.registration).rid

/-- The actual lookup capability chooses Fresh only after querying the private set at the authenticated identity/one-time identifier. -/
def begin (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (history : State) :
    OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect) :=
  RegistrationAgreementExecutor.continueWith (peer.begin_registration_lookup control authenticated) fun lookup =>
    RegistrationAgreementExecutor.continueWith lookup.request fun requested =>
      RegistrationAgreementExecutor.continueWith (lookup.resume (history.contains (absBytes requested.bytes)))
        (RegistrationAgreementExecutor.drive 9)

/-- Membership is derived from the actual source request; consumed identifiers reject before every agreement primitive callback. -/
theorem begin_eq (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (history : State) :
    begin control authenticated history =
      if history.contains (identifier authenticated) then pure (.ok (.Rejected .None))
      else RegistrationAgreementExecutor.server control .Fresh authenticated := by
  obtain ⟨requested, requestedRun, bytes⟩ := registration_id_abs authenticated.registration
  simp only [begin, peer.begin_registration_lookup, RegistrationAgreementExecutor.continueWith,
    peer.RegistrationLookup.request, registration.AuthenticatedInit.registration_id, requestedRun,
    bytes, identifier]
  change RegistrationAgreementExecutor.continueWith
      ((⟨control, authenticated⟩ : peer.RegistrationLookup).resume (history.contains (identifier authenticated)))
      (RegistrationAgreementExecutor.drive 9) =
        if history.contains (identifier authenticated) then pure (.ok (.Rejected .None))
        else RegistrationAgreementExecutor.server control .Fresh authenticated
  cases consumed : history.contains (identifier authenticated) <;>
    simp only [peer.RegistrationLookup.resume, Bool.false_eq_true, ite_false, ite_true,
      RegistrationAgreementExecutor.continueWith, RegistrationAgreementExecutor.server,
      RegistrationAgreementExecutor.drive, RegistrationAgreementExecutor.step, pure_bind]

/-- Actual successful root agreement yields a one-use response capability only after insertion of its retained native registration identifier. -/
def consume (accepted : agreement.ServerAgreement) (history : State) :
    RustM (core.option.Option peer.ConsumedRegistration × State) := do
  let pending ← peer.begin_registration_insert accepted
  let requested ← pending.request
  let present := history.contains (absBytes requested.bytes)
  let consumed ← pending.resume (!present)
  pure (consumed, if present then history else history ++ [absBytes requested.bytes])

/-- Successful actual insertion consumes the identifier before the first-record or signing controller runs. -/
theorem consume_fresh (accepted : agreement.ServerAgreement) (history : State)
    (fresh : history.contains (absBytes accepted.pending.registration_id.bytes) = false) :
    consume accepted history = .ok (.Some ⟨accepted⟩, history ++ [absBytes accepted.pending.registration_id.bytes]) := by
  simp only [consume, peer.begin_registration_insert,
    BeaconcryptCore.Refinement.PeerOwnership.registration_insert_request,
    BeaconcryptCore.Refinement.PeerOwnership.registration_insert_resume, bind_tc_ok, fresh,
    Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
  rfl

/-- A second insertion cannot recover a consumed capability or change the persistent set. -/
theorem consume_replayed (accepted : agreement.ServerAgreement) (history : State)
    (present : history.contains (absBytes accepted.pending.registration_id.bytes) = true) :
    consume accepted history = .ok (.None, history) := by
  simp only [consume, peer.begin_registration_insert,
    BeaconcryptCore.Refinement.PeerOwnership.registration_insert_request,
    BeaconcryptCore.Refinement.PeerOwnership.registration_insert_resume, bind_tc_ok, present,
    Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
  rfl

/-- Later source completion receives only its own state, with no replay-set read/write capability. -/
def consumeThen {Auxiliary Result : Type} (accepted : agreement.ServerAgreement)
    (post : peer.ConsumedRegistration → StateT Auxiliary ProbComp (RustM Result)) :
    StateT (State × Auxiliary) ProbComp (RustM (core.option.Option Result)) := fun before =>
  match consume accepted before.1 with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.None, history) => pure (.ok .None, (history, before.2))
  | .ok (.Some consumed, history) =>
      (fun result => (core.option.Option.Some <$> result.1, (history, result.2))) <$> (post consumed).run before.2

/-- A fresh native capability is consumed before the entire actual completion/signing/publication computation, regardless of that computation's final RustM outcome. -/
theorem consumeThen_fresh {Auxiliary Result : Type} (accepted : agreement.ServerAgreement)
    (post : peer.ConsumedRegistration → StateT Auxiliary ProbComp (RustM Result))
    (history : State) (auxiliary : Auxiliary)
    (fresh : history.contains (absBytes accepted.pending.registration_id.bytes) = false) :
    (consumeThen accepted post).run (history, auxiliary) =
      (fun result => (core.option.Option.Some <$> result.1,
        (history ++ [absBytes accepted.pending.registration_id.bytes], result.2))) <$>
          (post ⟨accepted⟩).run auxiliary := by
  simp only [consumeThen, StateT.run, consume_fresh accepted history fresh]

/-- Every later outcome retains the consumed set even when the actual post-root source returns fail, divergence, or an ordinary protocol rejection. -/
theorem consumed_persists {Auxiliary Result : Type} (accepted : agreement.ServerAgreement)
    (post : peer.ConsumedRegistration → StateT Auxiliary ProbComp (RustM Result))
    (history : State) (auxiliary : Auxiliary)
    (fresh : history.contains (absBytes accepted.pending.registration_id.bytes) = false)
    (result : RustM (core.option.Option Result) × (State × Auxiliary))
    (supported : result ∈ support ((consumeThen accepted post).run (history, auxiliary))) :
    result.2.1 = history ++ [absBytes accepted.pending.registration_id.bytes] := by
  rw [consumeThen_fresh accepted post history auxiliary fresh] at supported
  obtain ⟨inner, _possible, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  rfl

end BeaconcryptCore.Computational.RegistrationReplaySchedule

/-- info: 'BeaconcryptCore.Computational.RegistrationReplaySchedule.begin_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationReplaySchedule.begin_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationReplaySchedule.consume_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationReplaySchedule.consume_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationReplaySchedule.consume_replayed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationReplaySchedule.consume_replayed

/-- info: 'BeaconcryptCore.Computational.RegistrationReplaySchedule.consumeThen_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationReplaySchedule.consumeThen_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationReplaySchedule.consumed_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationReplaySchedule.consumed_persists
