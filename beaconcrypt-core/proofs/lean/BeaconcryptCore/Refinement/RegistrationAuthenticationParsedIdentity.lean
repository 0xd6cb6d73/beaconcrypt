-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCredentialMetadata
import BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation
import BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual source identity-copy and untagging operations coincide. The Core authentication invariant retains that exact key through every successful callback, allowing a separate actual Ed parse/open interpretation to derive a reparse receipt. -/
namespace BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity
theorem copy_dictionary : registration.InitMldsaVerification.resume.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 =
    pqxdh.untag_sign_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 := rfl

def Matches (encoded : Std.Array U8 33#usize) (key : Std.Array U8 32#usize) : Prop :=
  encoded.val[0]! = pqxdh.SIGN_TYPE_ED25519 ∧
    core.array.from_fn 32#usize registration.InitMldsaVerification.resume.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 encoded = .ok key

theorem matches_of_values (encoded : Std.Array U8 33#usize) (key : Std.Array U8 32#usize)
    (tagged : encoded.val[0]! = pqxdh.SIGN_TYPE_ED25519)
    (bytes : key.val = (List.range (32#usize).val).map (fun index => encoded.val[index + 1]!)) : Matches encoded key := by
  obtain ⟨copied, actual, copiedBytes⟩ := RegistrationAuthentication.identity_tail_exact encoded
  have same : copied = key := Subtype.ext (copiedBytes.trans bytes.symm)
  exact ⟨tagged, same ▸ actual⟩

theorem untag (encoded : Std.Array U8 33#usize) (key : Std.Array U8 32#usize) (matching : Matches encoded key) :
    pqxdh.untag_sign_key encoded = .ok (.Some key) := by
  unfold pqxdh.untag_sign_key
  rw [index_usize_eq encoded 0#usize (by scalar_tac)]
  simp only [bind_tc_ok, usize_val_0, matching.1, ↓reduceIte]
  rw [← copy_dictionary, matching.2]
  rfl

theorem validated (input : pqxdh.InitKex) (key : Std.Array U8 32#usize) (matching : Matches input.identity_key key)
    (verified : pqxdh.VerifiedInitKex) (actual : pqxdh.validate_init_kex input = .ok (.Ok verified)) :
    verified.beacon_identity_public_key = key := by
  obtain ⟨pre, preRun⟩ := BeaconcryptCore.PanicFreedom.untag_x25519_key_ok input.prekey pqxdh.KEY_ROLE_PREKEY
  obtain ⟨one, oneRun⟩ := BeaconcryptCore.PanicFreedom.untag_x25519_key_ok input.one_time_key pqxdh.KEY_ROLE_ONE_TIME
  obtain ⟨pq, pqRun⟩ := BeaconcryptCore.PanicFreedom.untag_mlkem768_key_ok input.pq_key
  unfold pqxdh.validate_init_kex at actual
  rw [untag input.identity_key key matching] at actual
  cases pre <;> cases one <;> cases pq <;>
    simp only [bind_tc_ok, preRun, oneRun, pqRun, reduceCtorEq, RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
  cases actual
  rfl

open RegistrationAuthentication RegistrationInbound RegistrationAuthenticationFlow

def Invariant (valid : Std.Array U8 32#usize → Prop) : registration.InitAuthentication → Prop
  | .HashRequested _ | .MldsaVerificationRequested _ | .Rejected => True
  | .Ed25519VerificationRequested pending => Matches pending.state.packet.identity_key pending.public_key
  | .ServerFingerprintRequested pending => valid pending.registration.beacon_identity_public_key
  | .BeaconFingerprintRequested pending => valid pending.registration.beacon_identity_public_key
  | .Accepted authenticated => valid authenticated.binding.beacon_identity_public_key

def ReplyValid (valid : Std.Array U8 32#usize → Prop) : registration.InitAuthentication → Event → Prop
  | .Ed25519VerificationRequested pending, .ed25519 _ (.Some _) => valid pending.public_key
  | _, _ => True

private theorem ed (valid : Std.Array U8 32#usize → Prop) (before : registration.InitEd25519Verification)
    (opened : Opened) (after : registration.InitAuthentication)
    (prior : Invariant valid (.Ed25519VerificationRequested before))
    (admitted : ReplyValid valid (.Ed25519VerificationRequested before) (.ed25519 before.stage opened))
    (actual : before.resume opened = .ok after) : Invariant valid after := by
  obtain ⟨result, returned, progress⟩ := init_ed_resume_refines before opened
  have facts : edProgress before opened after := (RustM.ok.inj (returned.symm.trans actual)) ▸ progress
  cases after
  all_goals simp only [edProgress] at facts
  case Rejected => trivial
  case Ed25519VerificationRequested next =>
    obtain ⟨bytes, _reply, _suffix, stateSame, keySame, _transition⟩ := facts
    simpa only [Invariant, stateSame, keySame] using prior
  case ServerFingerprintRequested next =>
    obtain ⟨bytes, reply, _suffix, _stage, _state, key, _keyBytes, validation⟩ := facts
    have same := validated ⟨before.state.packet.identity_key, before.pre_key, key, before.pq_key⟩
      before.public_key prior next.registration validation
    rw [reply] at admitted
    simpa only [Invariant, same, ReplyValid] using admitted

theorem progress (valid : Std.Array U8 32#usize → Prop) {before after : registration.InitAuthentication}
    {event : Event} (edge : Step before event after) (prior : Invariant valid before)
    (admitted : ReplyValid valid before event) : Invariant valid after := by
  cases edge with
  | ed25519 before opened after actual => exact ed valid before opened after prior admitted actual
  | hash before reply after actual =>
    cases reply with
    | none => exact (RustM.ok.inj actual) ▸ True.intro
    | some digest =>
      obtain ⟨next, returned, _packet, _pin, _digest, _input⟩ := init_hash_success before digest
      exact (RustM.ok.inj (returned.symm.trans actual)) ▸ True.intro
  | mldsa before verified after actual =>
    obtain ⟨result, returned, outcome⟩ := init_mldsa_exact before verified
    have facts : initMldsaOutcome before verified after := (RustM.ok.inj (returned.symm.trans actual)) ▸ outcome
    cases after
    all_goals simp only [initMldsaOutcome] at facts
    case Rejected => trivial
    case Ed25519VerificationRequested next =>
      obtain ⟨_verified, tagged, stateSame, _stage, bytes⟩ := facts
      simpa only [Invariant, stateSame] using matches_of_values before.state.packet.identity_key next.public_key tagged bytes
  | serverFingerprint before reply after actual =>
    cases reply with
    | none => exact (RustM.ok.inj actual) ▸ True.intro
    | some digest =>
      obtain ⟨next, returned, _state, same, _binding, _key, _fingerprint⟩ := init_server_fingerprint_exact before digest
      exact (RustM.ok.inj (returned.symm.trans actual)) ▸
        (show Invariant valid (.BeaconFingerprintRequested next) from by simpa only [Invariant, same] using prior)
  | beaconFingerprint before reply after actual =>
    cases reply with
    | none => exact (RustM.ok.inj actual) ▸ True.intro
    | some digest =>
      obtain ⟨accepted, returned, _registration, _pin, _digest, identity, _fingerprint, _ad⟩ :=
        init_beacon_fingerprint_exact before digest
      exact (RustM.ok.inj (returned.symm.trans actual)) ▸
        (show Invariant valid (.Accepted accepted) from by simpa only [Invariant, identity] using prior)

theorem initial (valid : Std.Array U8 32#usize → Prop) (pin : session.ServerAuthenticationPin)
    (packet : registration.InitPacket) (phase : registration.InitAuthentication)
    (actual : registration.begin_init_authentication pin packet = .ok phase) : Invariant valid phase := by
  obtain ⟨initial, started, _packet, _pin, _input⟩ := begin_init_exact pin packet
  cases RustM.ok.inj (started.symm.trans actual)
  trivial
end BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.copy_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.copy_dictionary

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.matches_of_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.matches_of_values

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.untag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.untag

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.validated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.validated

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.progress

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.initial
