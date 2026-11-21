-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthentication
import BeaconcryptCore.Refinement.RegistrationInbound

/-!
Finite executions of current registration version 3 use the actual request hash and three Ed25519 verification continuations. They accept arbitrary presented classical identities; no Beacon ML credential or enrollment premise exists. Events describe primitive replies, not primitive security or a native scheduler theorem.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationInbound

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

abbrev Digest := Array Std.U8 64#usize
abbrev Opened := core.option.Option (Slice Std.U8)

inductive Event where
  | hash (reply : core.option.Option Digest)
  | ed25519 (stage : registration.SignedKeyStage) (opened : Opened)

/-- Each edge is the actual extracted continuation with its retained capability. -/
inductive Step : registration.InitAuthentication → Event → registration.InitAuthentication → Prop where
  | hash (before : registration.InitHash) (reply : core.option.Option Digest) (after)
      (run : before.resume reply = ok after) :
      Step (.HashRequested before) (.hash reply) after
  | ed25519 (before : registration.InitEd25519Verification) (opened : Opened) (after)
      (run : before.resume opened = ok after) :
      Step (.Ed25519VerificationRequested before) (.ed25519 before.stage opened) after

inductive Run : registration.InitAuthentication → List Event → registration.InitAuthentication → Prop where
  | refl (state) : Run state [] state
  | step {start before after events event} (previous : Run start events before)
      (edge : Step before event after) : Run start (events ++ [event]) after

def Executes (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (final : registration.InitAuthentication) : Prop :=
  ∃ initial, registration.begin_init_authentication pin packet = ok initial ∧ Run initial events final

/-- Current successful request validation has one digest and exactly three opened attached fields. -/
def ValidatedRequestHistory (packet : registration.InitPacket) (events : List Event) : Prop :=
  ∃ (digest : Digest) (pq pre oneTime : Slice Std.U8),
    events = [.hash (.Some digest), .ed25519 .PqKey (.Some pq),
      .ed25519 .PreKey (.Some pre), .ed25519 .OneTimeKey (.Some oneTime)] ∧
    pq.val = packet.pq_key.val.drop 64 ∧ pre.val = packet.pre_key.val.drop 64 ∧
    oneTime.val = packet.one_time_key.val.drop 64

/-- Every live phase retains the entry pin and complete owned signed request buffers. -/
inductive Prefix (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    List Event → registration.InitAuthentication → Prop where
  | hash (before : registration.InitHash)
      (fieldsSame : before.fields = ownedFields packet) (pinSame : before.server_pin = pin) :
      Prefix pin packet [] (.HashRequested before)
  | pq (before : registration.InitEd25519Verification) (digest : Digest)
      (fieldsSame : before.state.fields = ownedFields packet)
      (pinSame : before.state.server_pin = pin) (digestSame : before.state.init_hash = digest)
      (stage : before.stage = .PqKey) :
      Prefix pin packet [.hash (.Some digest)] (.Ed25519VerificationRequested before)
  | pre (before : registration.InitEd25519Verification) (digest : Digest) (pq : Slice Std.U8)
      (fieldsSame : before.state.fields = ownedFields packet)
      (pinSame : before.state.server_pin = pin) (digestSame : before.state.init_hash = digest)
      (stage : before.stage = .PreKey) (pqSuffix : pq.val = packet.pq_key.val.drop 64) :
      Prefix pin packet [.hash (.Some digest), .ed25519 .PqKey (.Some pq)]
        (.Ed25519VerificationRequested before)
  | oneTime (before : registration.InitEd25519Verification) (digest : Digest) (pq pre : Slice Std.U8)
      (fieldsSame : before.state.fields = ownedFields packet)
      (pinSame : before.state.server_pin = pin) (digestSame : before.state.init_hash = digest)
      (stage : before.stage = .OneTimeKey) (pqSuffix : pq.val = packet.pq_key.val.drop 64)
      (preSuffix : pre.val = packet.pre_key.val.drop 64) :
      Prefix pin packet [.hash (.Some digest), .ed25519 .PqKey (.Some pq),
        .ed25519 .PreKey (.Some pre)] (.Ed25519VerificationRequested before)
  | accepted (events : List Event) (accepted : registration.AuthenticatedInit)
      (checks : ValidatedRequestHistory packet events)
      (retained : accepted.binding.server_pin = pin ∧ accepted.binding.init_fields = ownedFields packet)
      (recorded : ∃ tail, events = .hash (.Some accepted.binding.init_hash) :: tail) :
      Prefix pin packet events (.Accepted accepted)
  | rejected (events : List Event) : Prefix pin packet events .Rejected

private theorem ed_step_preserves (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (before : registration.InitEd25519Verification) (opened : Opened)
    (after : registration.InitAuthentication)
    (prior : Prefix pin packet events (.Ed25519VerificationRequested before))
    (run : before.resume opened = ok after) :
    Prefix pin packet (events ++ [.ed25519 before.stage opened]) after := by
  obtain ⟨result, resultRun, progress⟩ := init_ed_resume_refines before opened
  have facts : edProgress before opened after :=
    (RustM.ok.inj (resultRun.symm.trans run)) ▸ progress
  clear resultRun progress result
  cases after
  all_goals simp only [edProgress] at facts
  case Rejected => exact Prefix.rejected _
  case Ed25519VerificationRequested next =>
    obtain ⟨bytes, rfl, suffix, stateSame, keySame, transition⟩ := facts
    cases prior
    all_goals simp_all [edSignedBytes, ownedFields]
    case pq digest fieldsSame pinSame digestSame stage =>
      exact Prefix.pre next digest bytes
        ((congrArg (fun state => state.fields) stateSame).trans fieldsSame)
        ((congrArg (fun state => state.server_pin) stateSame).trans pinSame)
        ((congrArg (fun state => state.init_hash) stateSame).trans digestSame) transition.1 suffix
    case pre digest pq pqSuffix fieldsSame pinSame digestSame stage =>
      exact Prefix.oneTime next digest pq bytes
        ((congrArg (fun state => state.fields) stateSame).trans fieldsSame)
        ((congrArg (fun state => state.server_pin) stateSame).trans pinSame)
        ((congrArg (fun state => state.init_hash) stateSame).trans digestSame) transition.1 pqSuffix suffix
  case Accepted next =>
    obtain ⟨bytes, rfl, suffix, stageSame, key, keyBytes, validation, pinSame, digestSame, fieldsSame⟩ := facts
    cases prior
    all_goals simp_all [edSignedBytes, ownedFields]
    case oneTime digest pq pre pqSuffix preSuffix fieldsInitial pinInitial digestInitial stage =>
      refine Prefix.accepted _ next ⟨digest, pq, pre, bytes, rfl, pqSuffix, preSuffix, suffix⟩
        ⟨pinSame, by simpa only [ownedFields] using fieldsSame⟩ ?_
      rw [digestSame]
      exact ⟨_, rfl⟩

private theorem step_preserves (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (before after : registration.InitAuthentication) (event : Event)
    (prior : Prefix pin packet events before) (edge : Step before event after) :
    Prefix pin packet (events ++ [event]) after := by
  cases edge
  case ed25519 before opened run =>
    exact ed_step_preserves pin packet events before opened after prior run
  case hash before reply run =>
    cases prior with
    | hash _ fieldsSame pinSame =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ Prefix.rejected _
      | some digest =>
        obtain ⟨result, resultRun, outcome⟩ := init_hash_resume_refines before digest
        have same : result = after := RustM.ok.inj (resultRun.symm.trans run)
        subst result
        cases after
        all_goals simp only [initHashOutcome] at outcome
        case Rejected => exact Prefix.rejected _
        case Ed25519VerificationRequested next =>
          exact Prefix.pq next digest (outcome.2.1.trans fieldsSame)
            (outcome.2.2.1.trans pinSame) outcome.2.2.2.1 outcome.2.2.2.2.1

/-- Prefix provenance holds for every finite execution of the current continuations. -/
theorem run_preserves_prefix {pin : session.ServerAuthenticationPin} {packet : registration.InitPacket}
    {start final : registration.InitAuthentication} {events : List Event}
    (run : Run start events final) (initial : Prefix pin packet [] start) : Prefix pin packet events final := by
  induction run
  case step before after events event previous edge ih =>
    exact step_preserves pin packet events before after event ih edge
  case refl => exact initial

/-- Acceptance validates the remaining classical fields in source order, without an enrollment premise. -/
theorem accepted_requires_classical_checks (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) : ValidatedRequestHistory packet events := by
  obtain ⟨initial, started, run⟩ := execution
  have initialPrefix : Prefix pin packet [] initial :=
    (begin_init_exact pin packet).elim fun next facts =>
      (RustM.ok.inj (facts.1.symm.trans started)) ▸ Prefix.hash next facts.2.1 facts.2.2.1
  cases run_preserves_prefix run initialPrefix with
  | accepted _ _ checks _ _ => exact checks

/-- The accepted capability retains the exact pin, all signed request fields and the hash reply recorded in its real trace. -/
theorem accepted_request_provenance (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) :
    accepted.binding.server_pin = pin ∧ accepted.binding.init_fields = ownedFields packet ∧
      ∃ tail, events = .hash (.Some accepted.binding.init_hash) :: tail := by
  obtain ⟨initial, started, run⟩ := execution
  have initialPrefix : Prefix pin packet [] initial :=
    (begin_init_exact pin packet).elim fun next facts =>
      (RustM.ok.inj (facts.1.symm.trans started)) ▸ Prefix.hash next facts.2.1 facts.2.2.1
  cases run_preserves_prefix run initialPrefix with
  | accepted _ _ _ retained recorded => exact ⟨retained.1, retained.2, recorded⟩

/-- Exactly four controller replies are consumed on every accepted finite run. -/
theorem accepted_callback_count (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) : events.length = 4 := by
  obtain ⟨_, _, _, _, rfl, _⟩ := accepted_requires_classical_checks pin packet events accepted execution
  rfl

end BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.run_preserves_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.run_preserves_prefix

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_requires_classical_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_requires_classical_checks

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_request_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_request_provenance

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_callback_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_callback_count
