-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperCopy
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor

/-! The actual selected public first-open loop decreases the source remaining-KDF rank at every continued iteration. Primitive failure/divergence and arbitrary transcript replacement remain literal results. Sufficient finite driving is proved equal to the original extracted loop. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop
open BeaconcryptCore.Computational
variable [PublicWrapperPlatform.Material] [beaconcrypt.ratchet.Operations]
abbrev Result := Option (alloc.vec.Vec U8) × U64 × beaconcrypt_public_wrapper.beacon.BeaconState
abbrev body := beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body

omit [PublicWrapperPlatform.Material] [beaconcrypt.ratchet.Operations] in
private theorem bind_cut {A B : Type} (first : RustM A) (next : A → RustM B) (result : B)
    (actual : (first >>= next) = .ok result) : ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | fail error | div => cases actual
  | ok value => exact ⟨value, rfl, actual⟩

omit [beaconcrypt.ratchet.Operations] in
private theorem resumed (value : RustM (core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted))
    (identifier : U64) (after : registration.BeaconInitialOpen)
    (actual : (do
      let result ← value
      match result with
      | .Ok next => .ok (.cont next : ControlFlow registration.BeaconInitialOpen Result)
      | .Err control => .ok (.done (none, identifier, .Aborted control))) = .ok (.cont after)) :
    value = .ok (.Ok after) := by
  cases value with
  | fail error | div => cases actual
  | ok result => cases result with
    | Err control => cases actual
    | Ok next => cases actual; rfl

theorem body_progress (identifier : U64) (before after : registration.BeaconInitialOpen)
    (actual : body identifier before = .ok (.cont after)) :
    RegistrationBeaconRecordExecutor.rank after < RegistrationBeaconRecordExecutor.rank before := by
  cases before with
  | KdfRequested pending =>
      obtain ⟨request, _, called⟩ := bind_cut _ _ _ actual
      obtain ⟨reply, _, continued⟩ := bind_cut _ _ _ called
      exact RegistrationBeaconRecordExecutor.kdf_rank pending (.Some reply) after (resumed _ identifier after continued)
  | CommitmentRequested pending =>
      simp only [body, beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body,
        registration.BeaconRecordCommitment.transcript_mut, bind_tc_ok] at actual
      obtain ⟨⟨digest, erased⟩, _, continued⟩ := bind_cut _ _ _ actual
      cases digest with
      | none =>
          have core := resumed _ identifier after continued
          exact RegistrationBeaconRecordExecutor.commitment_rank _ false after core
      | some digest =>
          obtain ⟨slice, _, continued⟩ := bind_cut _ _ _ continued
          obtain ⟨supplied, _, continued⟩ := bind_cut _ _ _ continued
          obtain ⟨other, _, continued⟩ := bind_cut _ _ _ continued
          obtain ⟨matched, _, continued⟩ := bind_cut _ _ _ continued
          exact RegistrationBeaconRecordExecutor.commitment_rank _ matched after (resumed _ identifier after continued)
  | AeadRequested pending =>
      obtain ⟨request, _, continued⟩ := bind_cut _ _ _ actual
      obtain ⟨plaintext, _, continued⟩ := bind_cut _ _ _ continued
      obtain ⟨borrowed, _, continued⟩ := bind_cut _ _ _ continued
      obtain ⟨finished, _, continued⟩ := bind_cut _ _ _ continued
      cases finished with
      | Err control => cases continued
      | Ok completed =>
          obtain ⟨parts, _, continued⟩ := bind_cut _ _ _ continued
          rcases parts with ⟨control, binding, kernel, application⟩
          obtain ⟨copied, _, continued⟩ := bind_cut _ _ _ continued
          obtain ⟨identifier, _, continued⟩ := bind_cut _ _ _ continued
          obtain ⟨manager, _, continued⟩ := bind_cut _ _ _ continued
          cases continued

def drive : Nat → U64 → registration.BeaconInitialOpen → RustM Result
  | 0, _, _ => .div
  | fuel + 1, identifier, effect => do
      let decision ← body identifier effect
      match decision with
      | .cont next => drive fuel identifier next
      | .done result => .ok result

theorem loop_specializes (fuel : Nat) (identifier : U64) (effect : registration.BeaconInitialOpen)
    (enough : RegistrationBeaconRecordExecutor.rank effect < fuel) :
    drive fuel identifier effect =
      beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop effect identifier := by
  induction fuel generalizing effect with
  | zero => omega
  | succ fuel ih =>
      change drive (fuel + 1) identifier effect = loop (body identifier) effect
      rw [drive, loop.eq_def]
      cases actual : body identifier effect with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done result => rfl
        | cont next =>
            have progress := body_progress identifier effect next actual
            change drive fuel identifier next = loop (body identifier) next
            exact ih next (by omega)

def execute (identifier : U64) (effect : registration.BeaconInitialOpen) : RustM Result :=
  drive (RegistrationBeaconRecordExecutor.rank effect + 1) identifier effect

theorem specializes (identifier : U64) (effect : registration.BeaconInitialOpen) :
    execute identifier effect =
      beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop effect identifier :=
  loop_specializes _ identifier effect (by omega)

end BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop.body_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop.body_progress

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop.loop_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop.loop_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop.specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop.specializes
