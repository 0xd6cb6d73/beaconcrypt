-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

/-!
The actual Init continuations retain the initially selected Server binding and ML public key. The fingerprint continuation replaces its fingerprint slot while preserving both selected operands. Successful authentication also retains exactly the digest supplied by the first actual hash callback. These operational field links need no primitive correctness assumption.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata

open RegistrationAuthentication RegistrationInbound RegistrationAuthenticationFlow

def Retains (selected original : session.ServerAuthenticationPin) : Prop :=
  selected.binding = original.binding ∧ selected.public_key = original.public_key

/-- Phase metadata relates the retained digest to the first actual callback event. -/
def Metadata (pin : session.ServerAuthenticationPin) (events : List Event) :
    registration.InitAuthentication → Prop
  | .HashRequested before => events = [] ∧ Retains before.server_pin pin
  | .MldsaVerificationRequested before => Retains before.state.server_pin pin ∧
      events.head? = some (.hash (.Some before.state.init_hash))
  | .Ed25519VerificationRequested before => Retains before.state.server_pin pin ∧
      events.head? = some (.hash (.Some before.state.init_hash))
  | .ServerFingerprintRequested before => Retains before.state.server_pin pin ∧
      events.head? = some (.hash (.Some before.state.init_hash))
  | .BeaconFingerprintRequested before => Retains before.server_pin pin ∧
      events.head? = some (.hash (.Some before.state.init_hash))
  | .Accepted accepted => Retains accepted.binding.server_pin pin ∧
      events.head? = some (.hash (.Some accepted.binding.init_hash))
  | .Rejected => True

private theorem append_head (events : List Event) (digest : Digest) (event : Event)
    (first : events.head? = some (.hash (.Some digest))) :
    (events ++ [event]).head? = some (.hash (.Some digest)) := by
  simp only [List.head?_append, first, Option.some_or]

private theorem ed_metadata (pin : session.ServerAuthenticationPin) (events : List Event)
    (before : registration.InitEd25519Verification) (opened : Opened)
    (after : registration.InitAuthentication)
    (prior : Metadata pin events (.Ed25519VerificationRequested before))
    (run : before.resume opened = ok after) :
    Metadata pin (events ++ [.ed25519 before.stage opened]) after := by
  obtain ⟨result, actual, progress⟩ := init_ed_resume_refines before opened
  have facts : edProgress before opened after := (RustM.ok.inj (actual.symm.trans run)) ▸ progress
  cases after
  all_goals simp only [edProgress] at facts
  case Rejected => trivial
  case Ed25519VerificationRequested next =>
    obtain ⟨_bytes, _reply, _suffix, stateSame, _key, _transition⟩ := facts
    exact ⟨by simpa only [stateSame] using prior.1,
      by simpa only [stateSame] using append_head events before.state.init_hash _ prior.2⟩
  case ServerFingerprintRequested next =>
    obtain ⟨_bytes, _reply, _suffix, _stage, stateSame, _validated⟩ := facts
    exact ⟨by simpa only [stateSame] using prior.1,
      by simpa only [stateSame] using append_head events before.state.init_hash _ prior.2⟩

/-- Every actual callback edge preserves selected pin operands and the initial hash receipt. -/
theorem step_metadata (pin : session.ServerAuthenticationPin) (events : List Event)
    (before after : registration.InitAuthentication) (event : Event)
    (prior : Metadata pin events before) (edge : Step before event after) :
    Metadata pin (events ++ [event]) after := by
  cases edge
  case ed25519 before opened run => exact ed_metadata pin events before opened after prior run
  case hash before reply run =>
    cases reply with
    | none => exact (RustM.ok.inj run) ▸ True.intro
    | some digest =>
      obtain ⟨next, resumed, _packet, selected, hashed, _input⟩ := init_hash_success before digest
      exact (RustM.ok.inj (resumed.symm.trans run)) ▸
        (show Metadata pin (events ++ [.hash (.Some digest)]) (.MldsaVerificationRequested next) from
          ⟨by simpa only [selected] using prior.2,
            by simp only [prior.1, List.nil_append, List.head?_cons, hashed]⟩)
  case mldsa before verified run =>
    obtain ⟨result, resumed, outcome⟩ := init_mldsa_exact before verified
    have facts : initMldsaOutcome before verified after :=
      (RustM.ok.inj (resumed.symm.trans run)) ▸ outcome
    cases after
    all_goals simp only [initMldsaOutcome] at facts
    case Rejected => trivial
    case Ed25519VerificationRequested next =>
      exact ⟨by simpa only [facts.2.2.1] using prior.1,
        by simpa only [facts.2.2.1] using append_head events before.state.init_hash _ prior.2⟩
  case serverFingerprint before reply run =>
    cases reply with
    | none => exact (RustM.ok.inj run) ▸ True.intro
    | some fingerprint =>
      obtain ⟨next, resumed, stateSame, _registration, binding, key, _fingerprint⟩ :=
        init_server_fingerprint_exact before fingerprint
      exact (RustM.ok.inj (resumed.symm.trans run)) ▸
        (show Metadata pin (events ++ [.serverFingerprint (.Some fingerprint)]) (.BeaconFingerprintRequested next) from
          ⟨⟨binding.trans prior.1.1, key.trans prior.1.2⟩,
            by simpa only [stateSame] using append_head events before.state.init_hash _ prior.2⟩)
  case beaconFingerprint before reply run =>
    cases reply with
    | none => exact (RustM.ok.inj run) ▸ True.intro
    | some fingerprint =>
      obtain ⟨accepted, resumed, _registration, selected, hashed, _identity, _fingerprint, _ad⟩ :=
        init_beacon_fingerprint_exact before fingerprint
      exact (RustM.ok.inj (resumed.symm.trans run)) ▸
        (show Metadata pin (events ++ [.beaconFingerprint (.Some fingerprint)]) (.Accepted accepted) from
          ⟨by simpa only [selected] using prior.1,
            by simpa only [hashed] using append_head events before.state.init_hash _ prior.2⟩)

/-- The field invariant holds through an arbitrary finite execution of the actual callbacks. -/
theorem run_metadata (pin : session.ServerAuthenticationPin)
    {start final : registration.InitAuthentication} {events : List Event}
    (run : Run start events final) (initial : Metadata pin [] start) : Metadata pin events final := by
  induction run with
  | refl => exact initial
  | step previous edge ih => exact step_metadata pin _ _ _ _ ih edge

/-- Successful whole Init authentication retains the selected Server binding/key and the original actual hash digest. -/
theorem accepted_metadata (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) :
    accepted.binding.server_pin.binding = pin.binding ∧
      accepted.binding.server_pin.public_key = pin.public_key ∧
      events.head? = some (.hash (.Some accepted.binding.init_hash)) := by
  obtain ⟨initial, started, run⟩ := execution
  obtain ⟨next, began, _packet, selected, _input⟩ := begin_init_exact pin packet
  have initialMetadata : Metadata pin [] initial :=
    (RustM.ok.inj (began.symm.trans started)) ▸
      (show Metadata pin [] (.HashRequested next) from ⟨rfl, by simp only [Retains, selected, and_self]⟩)
  exact ⟨(run_metadata pin run initialMetadata).1.1,
    (run_metadata pin run initialMetadata).1.2, (run_metadata pin run initialMetadata).2⟩

/-- The digest retained in an accepted binding is the digest of its actual first hash reply. -/
theorem accepted_digest (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit) (digest : Digest)
    (execution : Executes pin packet events (.Accepted accepted))
    (first : events.head? = some (.hash (.Some digest))) : accepted.binding.init_hash = digest := by
  simpa using (accepted_metadata pin packet events accepted execution).2.2.symm.trans first

end BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.step_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.step_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.run_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.run_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_digest
