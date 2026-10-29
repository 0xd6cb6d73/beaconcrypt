-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRawReceiveBridge

/-! The actual Beacon post-root controller executes its initial KDF and the existing byte receive service with the authenticated binding already installed in its record context. Final registration admission follows the consumed receive kernel; rejection and primitive representation failures retain their actual source outcomes and all shared primitive effects. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBeaconPostRootServices

open RegistrationRawReceiveBridge (Spec)
abbrev Result := RegistrationBeaconRecordExecutor.Result

def continueWith {Input : Type} (result : RustM Input) (next : Input → OracleComp Spec (RustM Result)) :
    OracleComp Spec (RustM Result) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

private theorem map_continueWith {Input : Type} (result : RustM Input)
    (next : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM Result)) :
    simulateQ RegistrationRawReceiveBridge.nativeAdapter (RegistrationBeaconRecordExecutor.continueWith result next) =
      continueWith result (fun value => simulateQ RegistrationRawReceiveBridge.nativeAdapter (next value)) := by
  cases result <;> rfl

def fromInitial (erased : Std.Array Std.U8 357#usize) (pending : registration.BeaconInitialKdf) :
    OracleComp Spec (RustM Result) :=
  continueWith pending.request fun request => do
    let response ← Spec.query (.inl (.initialKdf request))
    match response with
    | .None => pure (.ok (.Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩))
    | .Some response =>
        RawCtxInterpretedOpening.bindResult (pqxdh.concrete.resume_initial_ratchet_kdf pending.pending response) fun kernel =>
          RegistrationRawReceiveBridge.finishModel pending.agreement <$>
            simulateQ RegistrationRawReceiveBridge.modelAdapter
              (RecordEffectsReceiveProgram.receive erased kernel 1#u64 pending.agreement.application_ciphertext
                pending.agreement.binding.associated_data pending.agreement.candidate.server_binding.identity_key_id)

def beacon (erased : Std.Array Std.U8 357#usize) (agreement : agreement.BeaconAgreement) :
    OracleComp Spec (RustM Result) :=
  continueWith (registration.begin_beacon_completion agreement) (fromInitial erased)

theorem initial_exact (erased : Std.Array Std.U8 357#usize) (pending : registration.BeaconInitialKdf) :
    simulateQ RegistrationRawReceiveBridge.nativeAdapter (RegistrationBeaconRecordExecutor.fromInitial pending) =
      fromInitial erased pending := by
  simp only [RegistrationBeaconRecordExecutor.fromInitial, fromInitial, map_continueWith]
  apply congrArg (continueWith pending.request)
  funext request
  simp only [simulateQ_bind, simulateQ_spec_query, RegistrationRawReceiveBridge.nativeAdapter]
  apply bind_congr
  intro response
  cases response with
  | none =>
      simp only [registration.BeaconInitialKdf.resume, pqxdh.beacon_abort_candidate, bind_tc_ok, simulateQ_pure]
  | some response =>
      obtain ⟨kernel, kernelRun⟩ := BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok pending.pending response
      obtain ⟨effect, effectRun, metadata⟩ := BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.begin_metadata
        kernel pending.agreement.candidate.server_binding.identity_key_id 1#u64 pending.agreement.binding.associated_data
        pending.agreement.application_ciphertext
      have actualResume : pending.resume (.Some response) = registration.normalize_beacon_open pending.agreement effect := by
        simp only [beacon_initial_request_refines, kernelRun, effectRun, bind_tc_ok]
      rw [actualResume]
      simp only [kernelRun, RawCtxInterpretedOpening.bindResult, RecordEffectsReceiveProgram.receive,
        effectRun]
      have exactEffect := RegistrationRawReceiveBridge.normalized_exact erased pending.agreement effect metadata
      cases normalizedRun : registration.normalize_beacon_open pending.agreement effect with
      | ok result => cases result <;>
          simpa only [RegistrationRawReceiveBridge.normalized, RegistrationRawReceiveBridge.model, normalizedRun]
            using exactEffect
      | fail error =>
          simpa only [RegistrationRawReceiveBridge.normalized, RegistrationRawReceiveBridge.model, normalizedRun]
            using exactEffect
      | div =>
          simpa only [RegistrationRawReceiveBridge.normalized, RegistrationRawReceiveBridge.model, normalizedRun]
            using exactEffect

theorem beacon_exact (erased : Std.Array Std.U8 357#usize) (agreement : agreement.BeaconAgreement) :
    simulateQ RegistrationRawReceiveBridge.nativeAdapter (RegistrationBeaconRecordExecutor.begin agreement) =
      beacon erased agreement := by
  simp only [RegistrationBeaconRecordExecutor.begin, beacon, map_continueWith]
  apply congrArg (continueWith (registration.begin_beacon_completion agreement))
  funext initial
  exact initial_exact erased initial

theorem beacon_shared {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (erased : Std.Array Std.U8 357#usize) (agreement : agreement.BeaconAgreement)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RegistrationBeaconRecordExecutor.execute source writer agreement).run state =
      (simulateQ (RegistrationRawReceiveBridge.implementation source writer) (beacon erased agreement)).run state := by
  rw [RegistrationBeaconRecordExecutor.execute, ← RegistrationRawReceiveBridge.program_projection, beacon_exact erased]

end BeaconcryptCore.Computational.RegistrationBeaconPostRootServices

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPostRootServices.initial_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPostRootServices.initial_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPostRootServices.beacon_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPostRootServices.beacon_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPostRootServices.beacon_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPostRootServices.beacon_shared
