-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementNormal
import BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage
/-! The actual Beacon agreement retains the original pending Server identifier through every getter/resume edge, root-input clearing and optional failure. Rejected control and completed candidate identifiers are derived from the same Core run; no agreement or successful-primitive premise is used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconAgreementKey
open RegistrationAgreementExecutor
open BeaconcryptCore.Refinement.KeyAgreement

def InputKey (keyId : U64) : agreement.AgreementInput → Prop
  | .Server _ _ _ _ => False
  | .Beacon control _ _ _ => control.expected_server_binding.identity_key_id = keyId

def CandidateKey (keyId : U64) : agreement.AgreementCandidate → Prop
  | .Server _ _ => False
  | .Beacon candidate _ _ => candidate.server_binding.identity_key_id = keyId

def PhaseKey (keyId : U64) : agreement.AgreementEffect → Prop
  | .ConvertPublic pending => InputKey keyId pending.state.input
  | .ConvertSecret pending => InputKey keyId pending.state.input
  | .GenerateEphemeral pending => InputKey keyId pending.state.input
  | .Encapsulate pending => InputKey keyId pending.state.input
  | .Decapsulate pending => InputKey keyId pending.state.input
  | .Dh pending => InputKey keyId pending.state.input
  | .RootKdf pending => CandidateKey keyId pending.candidate
  | .Rejected .None => False
  | .Rejected (.Some aborted) => aborted.server_key_id = keyId
  | .ServerComplete _ => False
  | .BeaconComplete completed => completed.candidate.server_binding.identity_key_id = keyId

theorem prepare_binding (control : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (candidate : pqxdh.BeaconRegistrationCandidate) (returned : pqxdh.beacon_prepare_finish control inputs = .ok (.Ok candidate)) :
    candidate.server_binding = control.expected_server_binding := by
  unfold pqxdh.beacon_prepare_finish at returned
  cases compared : core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8
      control.expected_server_binding.identity_public_key inputs.response_server_identity with
  | fail error | div => simp [compared] at returned
  | ok matched =>
      simp only [compared, bind_tc_ok] at returned
      cases matched with
      | false => simp at returned
      | true =>
          simp only [ite_true] at returned
          cases root : pqxdh.build_root_key_input inputs.shared_secrets with
          | fail error | div => simp [root] at returned
          | ok result =>
              simp only [root, bind_tc_ok] at returned
              cases result with
              | Err error => simp at returned
              | Ok root =>
                  simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at returned
                  exact (congrArg pqxdh.BeaconRegistrationCandidate.server_binding returned).symm

theorem rejected_key (keyId : U64) (state : agreement.AgreementState) (prior : InputKey keyId state.input)
    (final : agreement.AgreementEffect) (returned : state.reject = .ok final) : PhaseKey keyId final := by
  rw [rejection_refines] at returned
  cases returned
  cases input : state.input with
  | Server control status verified binding => simp only [input, InputKey] at prior
  | Beacon control binding response application =>
      simp only [abortFor, PhaseKey]
      simpa only [InputKey, input] using prior

theorem finish_dh_key (keyId : U64) (state : agreement.AgreementState) (prior : InputKey keyId state.input)
    (final : agreement.AgreementEffect) (returned : agreement.finish_dh state = .ok final) : PhaseKey keyId final := by
  cases input : state.input with
  | Server control status verified binding => simp only [InputKey, input] at prior
  | Beacon control binding response application =>
      have key : control.expected_server_binding.identity_key_id = keyId := by simpa only [InputKey, input] using prior
      simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, input, bind_tc_ok] at returned
      let arguments : pqxdh.BeaconFinishInputs := ⟨response.identity_key, response.key_id,
        ⟨state.dh1.bytes, state.dh2.bytes, state.dh3.bytes, state.dh4.bytes, state.kem.bytes⟩⟩
      change (do
        let prepared ← pqxdh.beacon_prepare_finish control arguments
        match prepared with
        | .Ok candidate => .ok (agreement.AgreementEffect.RootKdf ⟨.Beacon candidate binding application⟩)
        | .Err _ => do
            let aborted ← pqxdh.beacon_abort_init control
            .ok (agreement.AgreementEffect.Rejected (.Some aborted))) = .ok final at returned
      cases prepared : pqxdh.beacon_prepare_finish control arguments with
      | fail error | div => simp [prepared] at returned
      | ok result =>
          simp only [prepared, bind_tc_ok] at returned
          cases result with
          | Err error =>
              simp only [pqxdh.beacon_abort_init, bind_tc_ok, RustM.ok.injEq] at returned
              cases returned
              exact key
          | Ok candidate =>
              cases RustM.ok.inj returned
              change candidate.server_binding.identity_key_id = keyId
              rw [prepare_binding control arguments candidate prepared]
              exact key

theorem progress (keyId : U64) {initial final : agreement.AgreementEffect} (edge : Step initial final)
    (prior : PhaseKey keyId initial) : PhaseKey keyId final := by
  cases edge with
  | convertPublic pending request reply final requested resumed =>
      cases reply with
      | none => exact rejected_key keyId pending.state prior final resumed
      | some converted =>
          simp only [agreement.PublicConversionPending.resume] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | convertSecret pending request reply final requested resumed =>
      cases reply with
      | false => exact rejected_key keyId pending.state prior final resumed
      | true =>
          cases input : pending.state.input with
          | Server control status verified binding => simp only [PhaseKey, InputKey, input] at prior
          | Beacon control binding response application =>
              simp only [agreement.SecretConversionPending.resume, ite_true, input] at resumed
              cases RustM.ok.inj resumed
              exact prior
  | generate pending request reply final requested resumed =>
      cases reply with
      | none => exact rejected_key keyId pending.state prior final resumed
      | some ephemeral =>
          simp only [agreement.EphemeralPending.resume] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | encapsulate pending request reply final requested resumed =>
      cases reply with
      | none => exact rejected_key keyId pending.state prior final resumed
      | some pair =>
          rcases pair with ⟨ciphertext, shared⟩
          simp only [agreement.EncapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | decapsulate pending request reply final requested resumed =>
      cases reply with
      | none => exact rejected_key keyId pending.state prior final resumed
      | some shared =>
          simp only [agreement.DecapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | dh pending request reply final requested resumed =>
      cases reply with
      | none => exact rejected_key keyId pending.state prior final resumed
      | some shared =>
          cases position : pending.position with
          | First | Second | Third =>
              simp only [agreement.DhPending.resume, position, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              exact prior
          | Fourth =>
              apply finish_dh_key keyId {pending.state with dh4 := ⟨shared⟩} prior final
              simpa only [agreement.DhPending.resume, position, ratchet.RatchetChain.from_bytes, bind_tc_ok] using resumed
  | root pending request reply final requested resumed =>
      cases candidate : pending.candidate with
      | Server accepted binding => simp only [PhaseKey, CandidateKey, candidate] at prior
      | Beacon accepted binding application =>
          have key : accepted.server_binding.identity_key_id = keyId := by simpa only [PhaseKey, CandidateKey, candidate] using prior
          cases reply <;>
            simp only [agreement.RootKdfPending.resume, candidate, pqxdh.beacon_abort_candidate,
              pqxdh.BeaconRegistrationCandidate.root_key_input_mut, pqxdh.RootKeyInput.clear,
              ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
          all_goals cases RustM.ok.inj resumed
          all_goals exact key
  | rejected aborted | server completed | beacon completed => exact prior

theorem run (keyId : U64) {initial final : agreement.AgreementEffect} (path : Run initial final)
    (prior : PhaseKey keyId initial) : PhaseKey keyId final := by
  induction path with
  | refl phase => exact prior
  | cons edge path ih => exact ih (progress keyId edge prior)

theorem entry_key (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_beacon_agreement authenticated = .ok initial) :
    PhaseKey authenticated.control.expected_server_binding.identity_key_id initial := by
  by_cases identityId : authenticated.control.expected_server_binding.identity_key_id =
    authenticated.binding.server_pin.binding.identity_key_id
  · by_cases identityKey : PqxdhRefinement.absBytes authenticated.control.expected_server_binding.identity_public_key =
      PqxdhRefinement.absBytes authenticated.binding.server_pin.binding.identity_public_key
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, agreement.AgreementState.new, ratchet.RatchetChain.from_bytes,
        pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      rfl
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      exact identityId.symm
  · have unequal : authenticated.control.expected_server_binding.identity_key_id.val ≠
        authenticated.binding.server_pin.binding.identity_key_id.val :=
      fun same => identityId (UScalar.eq_of_val_eq same)
    simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
      pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
      session.ServerAuthenticationPin.impl.binding, pqxdh.beacon_abort_init, unequal] at actual
    subst initial
    rfl

theorem beacon_key (authenticated : registration.AuthenticatedResponse) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (beacon authenticated)) :
    PhaseKey authenticated.control.expected_server_binding.identity_key_id final := by
  obtain ⟨initial, started, path⟩ := beacon_sound authenticated final supported
  exact run _ path (entry_key authenticated initial started)

end BeaconcryptCore.Computational.RegistrationBeaconAgreementKey

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.prepare_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.prepare_binding

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.rejected_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.rejected_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.finish_dh_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.finish_dh_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.progress

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.run

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.entry_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.entry_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.beacon_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementKey.beacon_key
