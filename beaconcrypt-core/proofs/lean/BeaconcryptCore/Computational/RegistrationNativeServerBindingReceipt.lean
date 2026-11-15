-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerReceipt
import BeaconcryptCore.Refinement.RegistrationAd

/-! The original Server completion carries the taken token's actual root into its actual initial capability. Response hash/sign/encoding preserves the full native SessionBinding, rather than its two-field record-world projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt
open PqxdhServerAuthExperiment (Setup Codec Checks)
open BeaconcryptCore.Refinement.RegistrationPublication (completedBinding)
open RegistrationSigningShared (SignReply)
variable {n : Nat} {ι KemSK Reader Response Encoded : Type} {base : OracleSpec ι}

/-- Successful lookup retains the literal moved agreement, caller pin/control and supplied application. -/
theorem lookup_fields (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (token : peer.ConsumedRegistration) (application : Slice U8) (lookup : peer.CompletionLookup)
    (actual : peer.begin_completion_lookup control pin token application = .ok (.Ok lookup)) :
    lookup.control = control ∧ lookup.pin = pin ∧ lookup.registration = token ∧ lookup.application = application := by
  cases next : pqxdh.server_next_key_id control with
  | fail error | div =>
      simp only [peer.begin_completion_lookup, next] at actual
      cases actual
  | ok result => cases result with
    | Err error =>
        simp only [peer.begin_completion_lookup, next, bind_tc_ok] at actual
        cases actual
    | Ok keyId =>
        simp only [peer.begin_completion_lookup, next, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
        cases actual
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- Actual initial admission rechecks the complete current owner pin and retains the exact root-derived initializer and application from the taken token. -/
theorem initial_root (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (capability : agreement.ServerAgreement)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability capability application initial) :
    BeaconcryptCore.Refinement.SessionBinding.sameServerPin capability.binding.server_pin pin ∧
      ∃ digest binding, capability.binding.complete digest = .ok binding ∧ initial.binding = binding ∧
      initial.application = application ∧
      pqxdh.concrete.start_server_candidate_ratchet_kdf initial.candidate capability.root.bytes = .ok initial.pending := by
  obtain ⟨pending, digest, selected, resumed⟩ := actual
  have admitted : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability capability application initial :=
    ⟨pending, digest, selected, resumed⟩
  have pinSame : BeaconcryptCore.Refinement.SessionBinding.sameServerPin capability.binding.server_pin pin := by
    by_contra changed
    rw [BeaconcryptCore.Refinement.RegistrationPublication.server_owner_rejects control pin availability capability application changed] at selected
    cases selected
  obtain ⟨reply, binding, complete, sameBinding, _consistent, _prepared⟩ :=
    BeaconcryptCore.Refinement.RegistrationAd.server_admission_binding
      control pin availability capability application initial admitted
  obtain ⟨next, ran, _candidate, sameApplication, _hash, _consistent⟩ :=
    BeaconcryptCore.Refinement.RegistrationAd.server_digest_completes_binding pending digest
  have nextSame : next = initial := by simpa using ran.symm.trans resumed
  have origin := BeaconcryptCore.Refinement.RegistrationAd.server_ad_origin
    control pin availability capability application pending selected
  refine ⟨pinSame, reply, binding, complete, sameBinding, ?_, ?_⟩
  · exact (nextSame ▸ sameApplication).trans origin.2.2.1
  · rw [BeaconcryptCore.Refinement.RegistrationAd.server_admission_pending
      control pin availability capability application initial admitted]
    simpa only [pqxdh.concrete.start_server_candidate_ratchet_kdf,
      pqxdh.ServerRegistrationCandidate.ratchet_initialization,
      pqxdh.concrete.start_server_ratchet_kdf, PqxdhInitialRatchetComplementarity.serverPending] using
      pqxdh.concrete.start_server_ratchet_kdf_exact capability.root.bytes

namespace Publication
open RegistrationWorldServerPublication

def Full (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse Encoded) : Prop :=
  published.binding = completedBinding pending.binding pending.candidate.key_id ∧
    published.kernel = pending.kernel ∧ published.control = pending.candidate.next_state

private theorem ready_full (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (ready encode pending)) :
    published.binding = completedBinding pending.binding pending.candidate.key_id ∧
      published.kernel = pending.kernel ∧ published.control = pending.candidate.next_state := by
  cases message : pending.message with
  | fail error | div => simp only [ready, message, continueWith, support_pure, Set.mem_singleton_iff] at supported; cases supported
  | ok view =>
      simp only [ready, message, continueWith, support_pure, Set.mem_singleton_iff] at supported
      rw [BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines] at supported
      cases encoded : encode view with
      | none => simp only [encoded] at supported; cases supported
      | some bytes =>
          simp only [encoded, RustM.ok.injEq, core.result.Result.Ok.injEq] at supported
          cases supported
          exact ⟨rfl, rfl, rfl⟩

private theorem signing_full (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (signing encode payload digest pending)) :
    published.binding = completedBinding pending.binding pending.candidate.key_id ∧
      published.kernel = pending.kernel ∧ published.control = pending.candidate.next_state := by
  have requested : pending.request = .ok ⟨pending.binding.server_pin.public_key, .Server, pending.input, authentication.SIGNING_CONTEXT⟩ := rfl
  simp only [signing, requested, continueWith, mem_support_bind_iff] at supported
  obtain ⟨signature, _signed, continued⟩ := supported
  cases signature with
  | none =>
      simp only [registration.ServerResponseSigning.resume, pqxdh.server_abort_candidate, continueResult] at continued
      cases continued
  | some signature =>
      obtain ⟨result, resumed, fields⟩ :=
        BeaconcryptCore.Refinement.RegistrationPublication.server_signature_admission_refines pending signature
      rw [resumed] at continued
      cases result with
      | Err previous => simp only [continueResult, support_pure, Set.mem_singleton_iff] at continued; cases continued
      | Ok completed =>
          obtain ⟨candidate, binding, kernel, _signature, _length⟩ := fields
          obtain ⟨metadata, consumed, control⟩ := ready_full encode completed published continued
          exact ⟨by simpa only [binding, candidate] using metadata, consumed.trans kernel,
            control.trans (congrArg pqxdh.ServerRegistrationCandidate.next_state candidate)⟩

/-- Every actual unsigned response hash/sign/encode path preserves the complete native session metadata and consumed kernel. -/
theorem program_full (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (program encode pending)) : Full pending published := by
  obtain ⟨request, requested, _bytes⟩ := BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  simp only [program, requested, continueWith, mem_support_bind_iff] at supported
  obtain ⟨digest, _hashed, continued⟩ := supported
  obtain ⟨next, resumed, candidate, binding, kernel, _ciphertext, _message, _request⟩ :=
    BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending
      (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed] at continued
  obtain ⟨metadata, consumed, control⟩ := signing_full encode ⟨.server, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩
    digest next published continued
  exact ⟨by simpa only [binding, candidate] using metadata, consumed.trans kernel,
    control.trans (congrArg pqxdh.ServerRegistrationCandidate.next_state candidate)⟩

/-- The actual stateful World signing result retains that same full binding before the record-world projection erases fields. -/
theorem world_full (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse Encoded)
    (before after : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (supported : (.ok (.Ok published), after) ∈ support
      ((RegistrationWorldServerCompletion.signing sign encode pending).run before)) : Full pending published := by
  simp only [RegistrationWorldServerCompletion.signing, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  have result : inner.1 = .ok (.Ok published) := congrArg Prod.fst same
  apply program_full encode pending published
  apply OracleComp.support_simulateQ_run'_subset (RegistrationWorldSigning.outgoing sign)
    (program encode pending) before.world
  rw [StateT.run'_eq, support_map]
  exact ⟨inner, possible, result⟩
end Publication

end BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.lookup_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.lookup_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.initial_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.initial_root
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.Publication.program_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.Publication.program_full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.Publication.world_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt.Publication.world_full
