-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRootInterpreter

/-! Actual typed response fields, not an assumed prepared credential, connect native Beacon root admission to the existing source Phase2 preparation. The native registration binding is retained separately from the classical core candidate. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationBeaconRootPreparation

open RegistrationAgreementExecutor
open RegistrationBeaconAgreementRoot (callbacks normalized finish state rejected)

def Fields (authenticated : registration.AuthenticatedResponse)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) : Prop :=
  input.response = authenticated ∧ input.ciphertext = authenticated.packet.public.kem_cipher_text ∧
    input.ephemeral = authenticated.packet.public.ephemeral_key ∧
    input.finishInputs.response_server_identity = authenticated.packet.public.identity_key ∧
    input.finishInputs.assigned_key_id = authenticated.packet.public.key_id

theorem collect_fields (authenticated : registration.AuthenticatedResponse)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
    (supported : some input ∈ support (simulateQ (callbacks authenticated)
      (PqxdhBeaconPhase2Preparation.collect () false true () []))) : Fields authenticated input := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_monadLift,
    OptionT.run_mk, OptionT.run_pure, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, callbacks,
    pure_bind, Option.elim_some] at supported
  repeat' first
    | (simp only [Option.elim_some, Option.elim_none,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, callbacks,
        pure_bind, bind_map_left, RegistrationAgreementRoot.option,
        Bool.false_eq_true, ite_true, ite_false, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Option.some.injEq, Option.some_ne_none] at supported)
    | (obtain ⟨reply, _, supported⟩ := supported; cases reply)
  all_goals simp_all [Fields]

theorem finish_admission (authenticated : registration.AuthenticatedResponse)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
    (fields : Fields authenticated input) :
    agreement.finish_dh (state authenticated input) = (do
      let accepted ← pqxdh.beacon_prepare_finish authenticated.pending.control input.finishInputs
      match accepted with
      | .Ok candidate => .ok (.RootKdf ⟨.Beacon candidate authenticated.pending.binding authenticated.packet.application⟩)
      | .Err _ => .ok (rejected authenticated)) := by
  simp only [state, agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok]
  have inputs : (⟨authenticated.packet.public.identity_key, authenticated.packet.public.key_id,
      input.finishInputs.shared_secrets⟩ : pqxdh.BeaconFinishInputs) = input.finishInputs := by
    rw [← fields.2.2.2.1, ← fields.2.2.2.2]
  rw [inputs]
  rfl

def afterPrepared (authenticated : registration.AuthenticatedResponse) :
    Option (PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse) →
      OracleComp Spec (RustM agreement.AgreementEffect)
  | none => pure (.ok (rejected authenticated))
  | some prepared => drive 2 (.RootKdf ⟨.Beacon prepared.candidate authenticated.pending.binding authenticated.packet.application⟩)

private theorem drive_rejected (fuel : Nat) (aborted : core.option.Option pqxdh.BeaconAborted) :
    drive fuel (.Rejected aborted) = pure (.ok (.Rejected aborted)) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [drive, step, pure_bind, continueWith, ih]

noncomputable def prepared (authenticated : registration.AuthenticatedResponse) : OracleComp Spec (RustM agreement.AgreementEffect) := do
  let prepared ← simulateQ (callbacks authenticated)
    (PqxdhBeaconPhase2Preparation.prepare authenticated.pending.control () false true () [])
  afterPrepared authenticated prepared

/-- Native root admission is reached only from the actual collected response and its exact callback results. -/
theorem normalized_prepared (authenticated : registration.AuthenticatedResponse) :
    normalized authenticated = prepared authenticated := by
  simp only [normalized, prepared, PqxdhBeaconPhase2Preparation.prepare, simulateQ_bind, bind_assoc]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  cases result with
  | none => simp only [simulateQ_pure, pure_bind, afterPrepared]
  | some input =>
      have fields := collect_fields authenticated input supported
      change finish authenticated input =
        (simulateQ (callbacks authenticated) (PqxdhBeaconPhase2Preparation.afterInputs authenticated.pending.control input) >>=
          afterPrepared authenticated)
      rw [finish, finish_admission authenticated input fields,
        PqxdhBeaconPhase2Preparation.normalPrepare_exact]
      simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind, simulateQ_spec_query,
        callbacks, pure_bind, simulateQ_pure]
      cases PqxdhBeaconPhase2Preparation.normalPrepare authenticated.pending.control input.finishInputs <;>
        simp only [bind_tc_ok, continueWith, afterPrepared, rejected, drive_rejected]

end BeaconcryptCore.Computational.RegistrationBeaconRootPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootPreparation.collect_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootPreparation.collect_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootPreparation.finish_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootPreparation.finish_admission

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootPreparation.normalized_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootPreparation.normalized_prepared
