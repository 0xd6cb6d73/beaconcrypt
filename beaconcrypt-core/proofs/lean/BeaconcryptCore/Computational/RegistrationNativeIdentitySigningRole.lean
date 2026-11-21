-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress
import BeaconcryptCore.Refinement.PqxdhProtocol

/-! The reduction recognizes the one-time signing slot from its literal public tagged message. Source beacon_start establishes distinct production role tags, and every actual Ed resume retains that source message tuple. This gives an executable slot test; neither a private bad-accept detector nor the challenged seed is an input. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole
open BeaconcryptCore.Refinement

def oneTime (message : Pqxdh.Bytes) : Bool := (Pqxdh.parseXTag Pqxdh.roleOtk message).isSome

def slot : registration.SignedKeyStage → Bool
  | .OneTimeKey => true
  | _ => false

def Tagged (started : pqxdh.BeaconStart) : Prop :=
  oneTime (absBytes started.message.prekey) = false ∧
  oneTime (absBytes started.message.one_time_key) = true ∧
  oneTime (absBytes started.message.pq_key) = false

/-- The original source tuple builder establishes its production tags for arbitrary represented raw public inputs. -/
theorem initial (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins) :
    ∃ started, pqxdh.beacon_start control inputs coins = .ok started ∧ Tagged started := by
  obtain ⟨identity, identityRun, _identityAbs⟩ := tag_sign_key_abs inputs.identity_public_key
  obtain ⟨prekey, prekeyRun, prekeyAbs⟩ := tag_x25519_key_abs pqxdh.KEY_ROLE_PREKEY inputs.prekey_public_key
  obtain ⟨oneTimeKey, oneTimeRun, oneTimeAbs⟩ := tag_x25519_key_abs pqxdh.KEY_ROLE_ONE_TIME coins.one_time_public_key
  obtain ⟨pqKey, pqRun, pqAbs⟩ := tag_mlkem768_key_abs inputs.pq_public_key
  refine ⟨⟨⟨control.expected_server_binding, inputs.identity_public_key⟩, ⟨identity, prekey, oneTimeKey, pqKey⟩⟩, ?_, ?_⟩
  · simp only [pqxdh.beacon_start, identityRun, prekeyRun, oneTimeRun, pqRun, bind_tc_ok]
  · simp [Tagged, oneTime, prekeyAbs, oneTimeAbs, pqAbs, Pqxdh.parseXTag, Pqxdh.tagX, Pqxdh.tagPQ,
      Pqxdh.rolePre, Pqxdh.roleOtk]

def EffectTagged : registration.BeaconInitEffect → Prop
  | .Ed25519SigningRequested next => Tagged next.state.started
  | .HashRequested next => Tagged next.state.started
  | _ => True

/-- The literal Core begin either rejects or enters signing with the actual source tag invariant. -/
theorem begin (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    ∃ effect, registration.begin_beacon_init control inputs coins pin = .ok effect ∧ EffectTagged effect := by
  obtain ⟨started, startedRun, tagged⟩ := initial control inputs coins
  obtain ⟨actual, actualRun, begun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin
  have same : actual = started := RustM.ok.inj (actualRun.symm.trans startedRun)
  subst actual
  rw [begun]
  split_ifs
  · exact ⟨_, rfl, trivial⟩
  · exact ⟨_, rfl, tagged⟩

/-- The actual current signing request identifies exactly the one-time source stage using only its public message bytes. -/
theorem request (pending : registration.BeaconEd25519Signing) (tagged : Tagged pending.state.started) :
    ∃ request, pending.request = .ok request ∧
      oneTime (TranscriptAuthParts.absSlice request.message) = slot pending.stage := by
  obtain ⟨request, requested, _key, _role, message⟩ := RegistrationSigning.ed_request_exact pending
  have bytes := congrArg (List.map absByte) message
  refine ⟨request, requested, ?_⟩
  cases stage : pending.stage <;> simp only [RegistrationSigning.signingMessageValues, stage] at bytes
  case PreKey => simpa only [TranscriptAuthParts.absSlice, stage, slot] using (congrArg oneTime bytes).trans tagged.1
  case OneTimeKey => simpa only [TranscriptAuthParts.absSlice, stage, slot] using (congrArg oneTime bytes).trans tagged.2.1
  case PqKey => simpa only [TranscriptAuthParts.absSlice, stage, slot] using (congrArg oneTime bytes).trans tagged.2.2

/-- Every actually admitted attached response retains the tuple used by the public role test; failures do not invent a new signing stage. -/
theorem preserved (pending : registration.BeaconEd25519Signing) (tagged : Tagged pending.state.started)
    (reply : core.option.Option (Slice U8)) (effect : registration.BeaconInitEffect)
    (resumed : pending.resume reply = .ok effect) : EffectTagged effect := by
  obtain ⟨actual, actualRun, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  have same : actual = effect := RustM.ok.inj (actualRun.symm.trans resumed)
  subst actual
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition] at facts
  case Ed25519SigningRequested next =>
    cases stage : pending.stage <;> simp only [stage] at facts
    case PreKey =>
      have retained := congrArg registration.BeaconInitState.started facts.2.2.2
      change next.state.started = pending.state.started at retained
      change Tagged next.state.started
      rw [retained]
      exact tagged
    case OneTimeKey =>
      have retained := congrArg registration.BeaconInitState.started facts.2.2.2
      change next.state.started = pending.state.started at retained
      change Tagged next.state.started
      rw [retained]
      exact tagged
    case PqKey => exact False.elim facts.2
  case HashRequested next =>
    have retained := congrArg registration.BeaconInitState.started facts.2.2.2
    change next.state.started = pending.state.started at retained
    change Tagged next.state.started
    rw [retained]
    exact tagged
  all_goals trivial

end BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.begin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.request
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole.preserved
