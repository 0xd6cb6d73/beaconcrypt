-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRawSealBridge
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared
import BeaconcryptCore.Computational.RecordEffectsReceiveBridge
import BeaconcryptCore.Refinement.RegistrationAd

/-!
Post-root services retain the actual authenticated binding as public metadata. The Server rechecks the complete current pin, executes the actual initial and ongoing KDF requests, and invokes the existing raw source sealing program with populated AD before sequence one is sealed. The Beacon's handle and native preparation metadata are updated before record admission. No kernel is reset after its first send or receive, and no ciphertext is resealed under a replacement AD.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationPostRootServices

open RegistrationRawSealBridge (Spec)

abbrev ServerResult := RegistrationServerRecordExecutor.Result

def continueWith {Input : Type} (result : RustM Input) (next : Input → OracleComp Spec (RustM ServerResult)) :
    OracleComp Spec (RustM ServerResult) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def continueResult {Input : Type} (result : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp Spec (RustM ServerResult)) : OracleComp Spec (RustM ServerResult) :=
  match result with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

private theorem map_continueWith {Input : Type} (result : RustM Input)
    (next : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM ServerResult)) :
    simulateQ RegistrationRawSealBridge.nativeAdapter (RegistrationServerRecordExecutor.continueWith result next) =
      continueWith result (fun value => simulateQ RegistrationRawSealBridge.nativeAdapter (next value)) := by
  cases result <;> rfl

private theorem map_continueResult {Input : Type} (result : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM ServerResult)) :
    simulateQ RegistrationRawSealBridge.nativeAdapter (RegistrationServerRecordExecutor.continueResult result next) =
      continueResult result (fun value => simulateQ RegistrationRawSealBridge.nativeAdapter (next value)) := by
  cases result with
  | ok result => cases result <;> rfl
  | fail => rfl
  | div => rfl

def fromRatchet (pending : registration.ServerInitialSeal) : OracleComp Spec (RustM ServerResult) :=
  continueWith pending.request fun request => do
    let response ← Spec.query (.inl (.ratchetKdf request))
    continueResult (pending.resume response) RegistrationRawSealBridge.model

def fromInitial (pending : registration.ServerInitialKdf) : OracleComp Spec (RustM ServerResult) :=
  continueWith pending.request fun request => do
    let response ← Spec.query (.inl (.initialKdf request))
    continueResult (pending.resume response) fromRatchet

def fromAd (pending : registration.ServerAdHash) : OracleComp Spec (RustM ServerResult) :=
  continueWith pending.request fun request => do
    let response ← Spec.query (.inl (.adHash request))
    continueResult (pending.resume response) fromInitial

def server (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8) :
    OracleComp Spec (RustM ServerResult) :=
  continueResult (registration.begin_server_completion control current availability agreement application) fromAd

private theorem ratchet_exact (pending : registration.ServerInitialSeal)
    (raw : pending.pending.pending.context.encoding = .Raw) :
    simulateQ RegistrationRawSealBridge.nativeAdapter (RegistrationServerRecordExecutor.fromRatchet pending) =
      fromRatchet pending := by
  simp only [RegistrationServerRecordExecutor.fromRatchet, fromRatchet, map_continueWith]
  apply congrArg (continueWith pending.request)
  funext request
  simp only [simulateQ_bind, simulateQ_spec_query, RegistrationRawSealBridge.nativeAdapter]
  apply bind_congr
  intro response
  cases response with
  | none =>
      simp only [registration.ServerInitialSeal.resume, pqxdh.server_abort_candidate, bind_tc_ok,
        RegistrationServerRecordExecutor.continueResult, continueResult, simulateQ_pure]
  | some response =>
      obtain ⟨next, resumed, _state, context, _sequence, _control⟩ := server_step_kdf_refines pending response
      simp only [resumed, RegistrationServerRecordExecutor.continueResult, continueResult]
      exact RegistrationRawSealBridge.model_exact next (by simpa only [context] using raw)

theorem initial_exact (pending : registration.ServerInitialKdf) :
    simulateQ RegistrationRawSealBridge.nativeAdapter (RegistrationServerRecordExecutor.fromInitial pending) =
      fromInitial pending := by
  simp only [RegistrationServerRecordExecutor.fromInitial, fromInitial, map_continueWith]
  apply congrArg (continueWith pending.request)
  funext request
  simp only [simulateQ_bind, simulateQ_spec_query, RegistrationRawSealBridge.nativeAdapter]
  apply bind_congr
  intro response
  cases response with
  | none =>
      simp only [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate, bind_tc_ok,
        RegistrationServerRecordExecutor.continueResult, continueResult, simulateQ_pure]
  | some response =>
      obtain ⟨kernel, bound, next, _initial, _bound, _bytes, resumed, _state, _entry, context, _sequence, _request⟩ :=
        server_kdf_prefix_refines pending response
      simp only [resumed, RegistrationServerRecordExecutor.continueResult, continueResult]
      exact ratchet_exact next (by rw [context]; rfl)

/-- The additional AD hash is retained as a real callback in the raw source projection. -/
theorem ad_exact (pending : registration.ServerAdHash) :
    simulateQ RegistrationRawSealBridge.nativeAdapter (RegistrationServerRecordExecutor.fromAd pending) =
      fromAd pending := by
  simp only [RegistrationServerRecordExecutor.fromAd, fromAd, map_continueWith]
  apply congrArg (continueWith pending.request)
  funext request
  simp only [simulateQ_bind, simulateQ_spec_query, RegistrationRawSealBridge.nativeAdapter]
  apply bind_congr
  intro response
  simp only [map_continueResult]
  apply congrArg (continueResult (pending.resume response))
  funext initial
  exact initial_exact initial

/-- The actual current-pin and allocator gates precede the prefix-aware raw service. -/
theorem server_exact (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8) :
    simulateQ RegistrationRawSealBridge.nativeAdapter
      (RegistrationServerRecordExecutor.begin control current availability agreement application) =
      server control current availability agreement application := by
  simp only [RegistrationServerRecordExecutor.begin, server, map_continueResult]
  apply congrArg (continueResult (registration.begin_server_completion control current availability agreement application))
  funext pending
  exact ad_exact pending

theorem server_shared {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RegistrationServerRecordExecutor.execute source writer control current availability agreement application).run state =
      (simulateQ (RegistrationRawSealBridge.implementation source writer)
        (server control current availability agreement application)).run state := by
  rw [RegistrationServerRecordExecutor.execute, ← RegistrationRawSealBridge.program_projection,
    server_exact]

/-- Actual selected AD completion precedes the request for the retained root at the fixed initial domain. -/
theorem server_root_request (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial) :
    initial.pending.request.input = agreement.root.bytes ∧ initial.pending.request.info = INITIAL_RATCHET_INFO := by
  rw [BeaconcryptCore.Refinement.RegistrationAd.server_admission_pending
    control current availability agreement application initial actual]
  exact ⟨rfl, rfl⟩

def boundCandidate (pending : registration.ServerInitialKdf) : pqxdh.ServerRegistrationCandidate :=
  pending.candidate

theorem bound_candidate_fields (pending : registration.ServerInitialKdf) :
    (boundCandidate pending).key_id = pending.candidate.key_id ∧
      (boundCandidate pending).next_state = pending.candidate.next_state ∧
      (boundCandidate pending).server_identity_public_key = pending.candidate.server_identity_public_key ∧
      (boundCandidate pending).ephemeral_public_key = pending.candidate.ephemeral_public_key ∧
      (boundCandidate pending).kem_ciphertext = pending.candidate.kem_ciphertext := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The source seal input is selected only after the actual two KDF replies. The completed binding supplies full AD before the sequence-one seal, retaining its exact native entry kernel and streamed ID prefix. -/
theorem initial_source_input (pending : registration.ServerInitialKdf)
    (initialResponse : pqxdh.concrete.InitialRatchetKdfResponse) (response : RatchetKdfResponse) :
    ∃ (kernel : ConcreteRatchetKernel) (next : registration.ServerInitialSeal) (selected : registration.ServerRecordAead),
      pqxdh.concrete.resume_initial_ratchet_kdf pending.pending initialResponse = .ok kernel ∧
      pending.resume (.Some initialResponse) = .ok (.Ok next) ∧
      next.pending.pending.entry = kernel ∧ next.resume (.Some response) = .ok (.Ok selected) ∧
      RegistrationRawSealBridge.inputOf selected.pending.seal =
        ⟨selected.pending.seal.material, 1#u64,
          PqxdhServerRegistrationPublication.firstContext (boundCandidate pending) pending.binding.associated_data
            (Pqxdh.LE64 pending.candidate.key_id.val ++ TranscriptAuthParts.absSlice pending.application)⟩ := by
  obtain ⟨kernel, bound, next, kernelRun, _boundRun, boundBytes, resumed, _state, entry, context, sequence, _request⟩ :=
    server_kdf_prefix_refines pending initialResponse
  obtain ⟨selected, selectedRun, _state, selectedContext, selectedSequence, _control⟩ :=
    server_step_kdf_refines next response
  have first : selected.pending.seal.sequence = 1#u64 := by
    apply Std.UScalar.eq_of_val_eq
    simpa only [selectedSequence, Std.UScalar.ofNatCore_val_eq] using sequence
  refine ⟨kernel, next, selected, kernelRun, resumed, entry, selectedRun, ?_⟩
  simp only [RegistrationRawSealBridge.inputOf, RegistrationRawSealBridge.plaintext,
    selectedContext, context, serverRecordContext, first,
    PqxdhServerRegistrationPublication.firstContext, boundCandidate, boundBytes]

def bindPrepared {Response Shared : Type} (binding : session.CompletedRegistrationBinding)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) : PqxdhBeaconPhase2Shared.Prepared Response Shared :=
  { pending with metadata := { pending.metadata with completed := binding } }

def bindNativePrepared {Response : Type} (binding : session.CompletedRegistrationBinding)
    (pending : PqxdhBeaconPhase2Preparation.Prepared Response) : PqxdhBeaconPhase2Preparation.Prepared Response :=
  { pending with binding := binding }

theorem prepared_fields {Response Shared : Type} (binding : session.CompletedRegistrationBinding)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) :
    (bindPrepared binding pending).metadata.associatedData = binding.associated_data ∧
      (bindPrepared binding pending).metadata.binding = pending.metadata.binding ∧
      (bindPrepared binding pending).metadata.assigned = pending.metadata.assigned ∧
      (bindPrepared binding pending).root = pending.root ∧
      (bindPrepared binding pending).response = pending.response :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem prepared_related {Response Shared : Type} (interpret : Shared → Std.Array Std.U8 32#usize)
    (binding : session.CompletedRegistrationBinding) (native : PqxdhBeaconPhase2Preparation.Prepared Response)
    (handles : PqxdhBeaconPhase2Shared.Prepared Response Shared)
    (related : PqxdhBeaconPhase2Shared.ReadyRel interpret native handles) :
    PqxdhBeaconPhase2Shared.ReadyRel interpret (bindNativePrepared binding native) (bindPrepared binding handles) := by
  obtain ⟨response, ciphertext, ephemeral, metadata, root⟩ := related
  refine ⟨response, ciphertext, ephemeral, ?_, root⟩
  exact congrArg (fun data : PqxdhBeaconPhase2Shared.Metadata =>
    { data with completed := binding }) metadata

theorem beacon_owner_ad {Response Shared : Type} (binding : session.CompletedRegistrationBinding)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) (kernel : ConcreteRatchetKernel) :
    (PqxdhBeaconPhase2Publication.localOwner
      (PqxdhBeaconPhase2Shared.clearedMetadata (bindPrepared binding pending).metadata) binding.associated_data kernel).owner.associatedData =
      absBytes binding.associated_data := rfl

end BeaconcryptCore.Computational.RegistrationPostRootServices

/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.initial_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.initial_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.server_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.server_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.server_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.server_shared
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.server_root_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.server_root_request
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.bound_candidate_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.bound_candidate_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.initial_source_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.initial_source_input
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.prepared_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.prepared_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.prepared_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.prepared_related
/-- info: 'BeaconcryptCore.Computational.RegistrationPostRootServices.beacon_owner_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPostRootServices.beacon_owner_ad
