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
/-- Untagging copies exactly the complete classical identity suffix. -/
theorem identity_tail_exact (encoded : Std.Array U8 33#usize) :
    ∃ key : Std.Array U8 32#usize,
      core.array.from_fn 32#usize pqxdh.untag_sign_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 encoded = .ok key ∧
      key.val = (List.range (32#usize).val).map (fun index => encoded.val[index + 1]!) := by
  apply from_fn_pure 32#usize pqxdh.untag_sign_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 encoded
    (fun index => encoded.val[index + 1]!)
  intro index inside
  rw [usize_val_32] at inside
  have indexValue : (⟨BitVec.ofNat _ index⟩ : Std.Usize).val = index := usize_mk_val index (by omega)
  obtain ⟨next, nextRun, nextValue⟩ := usize_add_val (⟨BitVec.ofNat _ index⟩ : Std.Usize) 1#usize
    (lt_numBits _ (by rw [indexValue, usize_val_1]; omega))
  rw [indexValue, usize_val_1] at nextValue
  simp only [Std.UScalarTy.numBits] at nextRun
  change (do
    let offset ← (⟨BitVec.ofNat System.Platform.numBits index⟩ : Std.Usize) + 1#usize
    let byte ← Std.Array.index_usize encoded offset
    ok (byte, encoded)) = ok (encoded.val[index + 1]!, encoded)
  rw [nextRun]
  simp only [bind_tc_ok]
  rw [index_usize_eq encoded next (by rw [nextValue, usize_val_33]; omega), nextValue]
  rfl

def Matches (encoded : Std.Array U8 33#usize) (key : Std.Array U8 32#usize) : Prop :=
  encoded.val[0]! = pqxdh.SIGN_TYPE_ED25519 ∧
    core.array.from_fn 32#usize pqxdh.untag_sign_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 encoded = .ok key

theorem matches_of_values (encoded : Std.Array U8 33#usize) (key : Std.Array U8 32#usize)
    (tagged : encoded.val[0]! = pqxdh.SIGN_TYPE_ED25519)
    (bytes : key.val = (List.range (32#usize).val).map (fun index => encoded.val[index + 1]!)) : Matches encoded key := by
  obtain ⟨copied, actual, copiedBytes⟩ := identity_tail_exact encoded
  have same : copied = key := Subtype.ext (copiedBytes.trans bytes.symm)
  exact ⟨tagged, same ▸ actual⟩

/-- The retained-field copy and the validated identity untagging read the same complete suffix. -/
theorem owned_identity (fields : authentication.OwnedInitFields) (key : Std.Array U8 32#usize)
    (matching : Matches fields.identity_key key) :
    authentication.OwnedInitFields.identity_public_key fields = .ok key := by
  obtain ⟨copied, copiedRun, copiedBytes⟩ := TranscriptAuthInputsRefinement.identity_public_key_exact fields
  obtain ⟨untagged, untaggedRun, untaggedBytes⟩ := identity_tail_exact fields.identity_key
  have same : untagged = key := RustM.ok.inj (untaggedRun.symm.trans matching.2)
  have exactCopy : copied = key := Subtype.ext
    (copiedBytes.trans (untaggedBytes.symm.trans (congrArg Subtype.val same)))
  exact exactCopy ▸ copiedRun

theorem untag (encoded : Std.Array U8 33#usize) (key : Std.Array U8 32#usize) (matching : Matches encoded key) :
    pqxdh.untag_sign_key encoded = .ok (.Some key) := by
  unfold pqxdh.untag_sign_key
  rw [index_usize_eq encoded 0#usize (by scalar_tac)]
  simp only [bind_tc_ok, usize_val_0, matching.1, ↓reduceIte]
  rw [matching.2]
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
  | .HashRequested _ | .Rejected => True
  | .Ed25519VerificationRequested pending => Matches pending.state.fields.identity_key pending.public_key
  | .Accepted authenticated => valid authenticated.registration.beacon_identity_public_key ∧
      authentication.OwnedInitFields.identity_public_key authenticated.binding.init_fields =
        .ok authenticated.registration.beacon_identity_public_key

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
  case Accepted next =>
    obtain ⟨bytes, reply, _suffix, _stage, key, _keyBytes, validation, _pin, _hash, fields⟩ := facts
    have same := validated ⟨before.state.fields.identity_key, before.pre_key, key, before.pq_key⟩
      before.public_key prior next.registration validation
    constructor
    · rw [reply] at admitted
      simpa only [same, ReplyValid] using admitted
    · rw [fields, same]
      exact owned_identity before.state.fields before.public_key prior

theorem progress (valid : Std.Array U8 32#usize → Prop) {before after : registration.InitAuthentication}
    {event : Event} (edge : Step before event after) (prior : Invariant valid before)
    (admitted : ReplyValid valid before event) : Invariant valid after := by
  cases edge with
  | ed25519 before opened after actual => exact ed valid before opened after prior admitted actual
  | hash before reply after actual =>
    cases reply with
    | none => exact (RustM.ok.inj actual) ▸ True.intro
    | some digest =>
      obtain ⟨result, returned, outcome⟩ := init_hash_resume_refines before digest
      have facts : initHashOutcome before digest after := (RustM.ok.inj (returned.symm.trans actual)) ▸ outcome
      cases after
      all_goals simp only [initHashOutcome] at facts
      case Rejected => trivial
      case Ed25519VerificationRequested next =>
        obtain ⟨tagged, fields, _pin, _digest, _stage, bytes⟩ := facts
        simpa only [Invariant, fields] using matches_of_values before.fields.identity_key next.public_key tagged bytes

theorem initial (valid : Std.Array U8 32#usize → Prop) (pin : session.ServerAuthenticationPin)
    (packet : registration.InitPacket) (phase : registration.InitAuthentication)
    (actual : registration.begin_init_authentication pin packet = .ok phase) : Invariant valid phase := by
  obtain ⟨initial, started, _packet, _pin, _input⟩ := begin_init_exact pin packet
  cases RustM.ok.inj (started.symm.trans actual)
  trivial
end BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity


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

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.owned_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.owned_identity

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.identity_tail_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity.identity_tail_exact
