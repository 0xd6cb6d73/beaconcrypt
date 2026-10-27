-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthentication
import BeaconcryptCore.Refinement.RegistrationInbound

/-!
Finite controller executions begin with the actual extracted Init entry point and retain the actual capabilities at every resume. Events describe replies supplied to the core; primitive correctness and the native scheduler are outside this relation.
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
  | mldsa (verified : Bool)
  | ed25519 (stage : registration.SignedKeyStage) (opened : Opened)
  | serverFingerprint (reply : core.option.Option Digest)
  | beaconFingerprint (reply : core.option.Option Digest)

/-- Each edge is an actual extracted continuation equation with its retained capability. -/
inductive Step : registration.InitAuthentication → Event → registration.InitAuthentication → Prop where
  | hash (before : registration.InitHash) (reply : core.option.Option Digest) (after)
      (run : before.resume reply = ok after) :
      Step (.HashRequested before) (.hash reply) after
  | mldsa (before : registration.InitMldsaVerification) (verified : Bool) (after)
      (run : before.resume verified = ok after) :
      Step (.MldsaVerificationRequested before) (.mldsa verified) after
  | ed25519 (before : registration.InitEd25519Verification) (opened : Opened) (after)
      (run : before.resume opened = ok after) :
      Step (.Ed25519VerificationRequested before) (.ed25519 before.stage opened) after
  | serverFingerprint (before : registration.InitServerFingerprint)
      (reply : core.option.Option Digest) (after) (run : before.resume reply = ok after) :
      Step (.ServerFingerprintRequested before) (.serverFingerprint reply) after
  | beaconFingerprint (before : registration.InitBeaconFingerprint)
      (reply : core.option.Option Digest) (after) (run : before.resume reply = ok after) :
      Step (.BeaconFingerprintRequested before) (.beaconFingerprint reply) after

inductive Run : registration.InitAuthentication → List Event → registration.InitAuthentication → Prop where
  | refl (state) : Run state [] state
  | step {start before after events event} (previous : Run start events before)
      (edge : Step before event after) : Run start (events ++ [event]) after

/-- Entry phases cannot be fabricated: every complete execution starts at the actual begin call. -/
def Executes (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (final : registration.InitAuthentication) : Prop :=
  ∃ initial, registration.begin_init_authentication pin packet = ok initial ∧ Run initial events final

/-- The successful callback history, including every required present reply and exact attached suffix. -/
def Gates (packet : registration.InitPacket) (events : List Event) : Prop :=
  ∃ (digest : Digest) (pq pre oneTime : Slice Std.U8) (serverFp beaconFp : Digest),
    events = [.hash (.Some digest), .mldsa true,
      .ed25519 .PqKey (.Some pq), .ed25519 .PreKey (.Some pre),
      .ed25519 .OneTimeKey (.Some oneTime), .serverFingerprint (.Some serverFp),
      .beaconFingerprint (.Some beaconFp)] ∧
    pq.val = packet.pq_key.val.drop 64 ∧ pre.val = packet.pre_key.val.drop 64 ∧
    oneTime.val = packet.one_time_key.val.drop 64

/-- Reachable phase prefixes retain the initial decoded packet and its complete gate history. -/
inductive Prefix (packet : registration.InitPacket) : List Event → registration.InitAuthentication → Prop where
  | hash (before : registration.InitHash) (packetSame : before.packet = packet) :
      Prefix packet [] (.HashRequested before)
  | mldsa (before : registration.InitMldsaVerification) (digest : Digest)
      (packetSame : before.state.packet = packet) :
      Prefix packet [.hash (.Some digest)] (.MldsaVerificationRequested before)
  | pq (before : registration.InitEd25519Verification) (digest : Digest)
      (packetSame : before.state.packet = packet) (stage : before.stage = .PqKey) :
      Prefix packet [.hash (.Some digest), .mldsa true] (.Ed25519VerificationRequested before)
  | pre (before : registration.InitEd25519Verification) (digest : Digest) (pq : Slice Std.U8)
      (packetSame : before.state.packet = packet) (stage : before.stage = .PreKey)
      (pqSuffix : pq.val = packet.pq_key.val.drop 64) :
      Prefix packet [.hash (.Some digest), .mldsa true, .ed25519 .PqKey (.Some pq)]
        (.Ed25519VerificationRequested before)
  | oneTime (before : registration.InitEd25519Verification) (digest : Digest) (pq pre : Slice Std.U8)
      (packetSame : before.state.packet = packet) (stage : before.stage = .OneTimeKey)
      (pqSuffix : pq.val = packet.pq_key.val.drop 64) (preSuffix : pre.val = packet.pre_key.val.drop 64) :
      Prefix packet [.hash (.Some digest), .mldsa true, .ed25519 .PqKey (.Some pq),
        .ed25519 .PreKey (.Some pre)] (.Ed25519VerificationRequested before)
  | serverFingerprint (before : registration.InitServerFingerprint) (digest : Digest)
      (pq pre oneTime : Slice Std.U8) (packetSame : before.state.packet = packet)
      (pqSuffix : pq.val = packet.pq_key.val.drop 64) (preSuffix : pre.val = packet.pre_key.val.drop 64)
      (oneTimeSuffix : oneTime.val = packet.one_time_key.val.drop 64) :
      Prefix packet [.hash (.Some digest), .mldsa true, .ed25519 .PqKey (.Some pq),
        .ed25519 .PreKey (.Some pre), .ed25519 .OneTimeKey (.Some oneTime)]
        (.ServerFingerprintRequested before)
  | beaconFingerprint (before : registration.InitBeaconFingerprint) (digest : Digest)
      (pq pre oneTime : Slice Std.U8) (serverFp : Digest) (packetSame : before.state.packet = packet)
      (pqSuffix : pq.val = packet.pq_key.val.drop 64) (preSuffix : pre.val = packet.pre_key.val.drop 64)
      (oneTimeSuffix : oneTime.val = packet.one_time_key.val.drop 64) :
      Prefix packet [.hash (.Some digest), .mldsa true, .ed25519 .PqKey (.Some pq),
        .ed25519 .PreKey (.Some pre), .ed25519 .OneTimeKey (.Some oneTime),
        .serverFingerprint (.Some serverFp)] (.BeaconFingerprintRequested before)
  | accepted (events : List Event) (accepted : registration.AuthenticatedInit) (gates : Gates packet events) :
      Prefix packet events (.Accepted accepted)
  | rejected (events : List Event) : Prefix packet events .Rejected

private theorem ed_step_preserves (packet : registration.InitPacket) (events : List Event)
    (before : registration.InitEd25519Verification) (opened : Opened)
    (after : registration.InitAuthentication)
    (prior : Prefix packet events (.Ed25519VerificationRequested before))
    (run : before.resume opened = ok after) :
    Prefix packet (events ++ [.ed25519 before.stage opened]) after := by
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
    all_goals simp_all [edSignedBytes]
    case pq digest packetSame stage =>
      exact Prefix.pre next digest bytes
        ((congrArg (fun state => state.packet) stateSame).trans packetSame) transition.1 suffix
    case pre digest pq pqSuffix packetSame stage =>
      exact Prefix.oneTime next digest pq bytes
        ((congrArg (fun state => state.packet) stateSame).trans packetSame) transition.1 pqSuffix suffix
  case ServerFingerprintRequested next =>
    obtain ⟨bytes, rfl, suffix, stageSame, stateSame, validation⟩ := facts
    cases prior
    all_goals simp_all [edSignedBytes]
    case oneTime digest pq pre pqSuffix preSuffix packetSame stage =>
      exact Prefix.serverFingerprint next digest pq pre bytes
        ((congrArg (fun state => state.packet) stateSame).trans packetSame) pqSuffix preSuffix suffix

private theorem step_preserves (packet : registration.InitPacket) (events : List Event)
    (before after : registration.InitAuthentication) (event : Event)
    (prior : Prefix packet events before) (edge : Step before event after) :
    Prefix packet (events ++ [event]) after := by
  cases edge
  case ed25519 before opened run =>
    exact ed_step_preserves packet events before opened after prior run
  case hash before reply run =>
    cases prior with
    | hash _ packetSame =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ Prefix.rejected _
      | some digest =>
        exact (init_hash_success before digest).elim fun next facts =>
          (RustM.ok.inj (facts.1.symm.trans run)) ▸
            Prefix.mldsa next digest (facts.2.1.trans packetSame)
  case mldsa before verified run =>
    cases prior with
    | mldsa _ digest packetSame =>
      have outcome : initMldsaOutcome before verified after :=
        (init_mldsa_exact before verified).elim fun result facts =>
          (RustM.ok.inj (facts.1.symm.trans run)) ▸ facts.2
      cases after
      all_goals simp only [initMldsaOutcome] at outcome
      case Ed25519VerificationRequested next =>
        exact outcome.1.symm ▸ Prefix.pq next digest
          ((congrArg (fun state => state.packet) outcome.2.2.1).trans packetSame) outcome.2.2.2.1
      case Rejected => exact Prefix.rejected _
  case serverFingerprint before reply run =>
    cases prior with
    | serverFingerprint _ digest pq pre oneTime packetSame pqSuffix preSuffix oneTimeSuffix =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ Prefix.rejected _
      | some fingerprint =>
        exact (init_server_fingerprint_exact before fingerprint).elim fun next facts =>
          (RustM.ok.inj (facts.1.symm.trans run)) ▸
            Prefix.beaconFingerprint next digest pq pre oneTime fingerprint
              ((congrArg (fun state => state.packet) facts.2.1).trans packetSame)
              pqSuffix preSuffix oneTimeSuffix
  case beaconFingerprint before reply run =>
    cases prior with
    | beaconFingerprint _ digest pq pre oneTime serverFp packetSame pqSuffix preSuffix oneTimeSuffix =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ Prefix.rejected _
      | some fingerprint =>
        exact (init_beacon_fingerprint_exact before fingerprint).elim fun accepted facts =>
          (RustM.ok.inj (facts.1.symm.trans run)) ▸
            Prefix.accepted _ accepted
              ⟨digest, pq, pre, oneTime, serverFp, fingerprint, rfl, pqSuffix, preSuffix, oneTimeSuffix⟩

/-- The prefix invariant holds for every finite execution of the actual continuations. -/
theorem run_preserves_prefix {packet : registration.InitPacket}
    {start final : registration.InitAuthentication} {events : List Event}
    (run : Run start events final) (initial : Prefix packet [] start) : Prefix packet events final := by
  induction run
  case step before after events event previous edge ih =>
    exact step_preserves packet events before after event ih edge
  case refl => exact initial

/-- Acceptance from the real entry point requires every gate, present reply and exact attached suffix in source order. -/
theorem accepted_requires_gates (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) : Gates packet events := by
  obtain ⟨initial, started, run⟩ := execution
  have initialPrefix : Prefix packet [] initial :=
    (begin_init_exact pin packet).elim fun next facts =>
      (RustM.ok.inj (facts.1.symm.trans started)) ▸ Prefix.hash next facts.2.1
  cases run_preserves_prefix run initialPrefix with
  | accepted _ _ gates => exact gates

/-- An accepted finite execution consumes exactly the seven required controller replies. -/
theorem accepted_callback_count (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) : events.length = 7 := by
  obtain ⟨_, _, _, _, _, _, rfl, _⟩ := accepted_requires_gates pin packet events accepted execution
  rfl

end BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.run_preserves_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.run_preserves_prefix

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_requires_gates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_requires_gates

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_callback_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_callback_count
