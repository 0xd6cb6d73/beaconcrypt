-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerRawSource

/-! Actual first-record sealing uses the fixed source AEAD and the source-selected LE64 assigned identifier followed by the original application. All operands are derived from reached source requests and optional replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerSealSource
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.PqxdhSurface
open BeaconcryptCore.Refinement.ProtocolComposition
open RegistrationNativeServerRecordTrace (Trace)
variable {n : Nat} {ι KemSK Auxiliary Reader Encoded S : Type} {base : OracleSpec ι}

private theorem opened (bytes : Pqxdh.Bytes) (result : Slice U8)
    (actual : RegistrationAuthenticationShared.openedBytes (some bytes) = .Some result) :
    TranscriptAuthParts.absSlice result = bytes := by
  simp only [RegistrationAuthenticationShared.openedBytes] at actual
  split at actual
  · cases actual
    simp only [TranscriptAuthParts.absSlice, List.map_map, Function.comp_def, absByte_concreteByte]
    change List.map id bytes = bytes
    exact List.map_id bytes
  · cases actual

private theorem sealed (pair : Pqxdh.Bytes × Pqxdh.Bytes) (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (actual : RegistrationRecordPrimitives.sealedBytes (some pair) = .Some (ciphertext, tag)) :
    TranscriptAuthParts.absSlice ciphertext = pair.1 ∧ absBytes tag = pair.2 := by
  simp only [RegistrationRecordPrimitives.sealedBytes] at actual
  split at actual
  · cases converted : RegistrationAuthenticationShared.openedBytes (some pair.1) with
    | none => simp only [converted] at actual; cases actual
    | some bytes =>
      simp only [converted] at actual
      have body := opened pair.1 bytes converted
      cases actual
      exact ⟨body, by simp [absBytes, List.map_map, Function.comp_def]⟩
  · cases actual

/-- Every actual successful detached seal reply is the actual fixed source AEAD ciphertext/tag. -/
theorem reply (setup : Setup base KemSK) (codec : Codec Reader Encoded)
    (request : record_effects.AeadSealRequest) (before after : RegistrationWorldAgreement.State n Auxiliary)
    (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (supported : (.Some (ciphertext, tag), after) ∈ support
      ((RegistrationWorldRecords.handler setup codec (.seal request)).run before)) :
    (TranscriptAuthParts.absSlice ciphertext, absBytes tag) =
      setup.source.crypto.aeadSeal (absBytes request.key) (absBytes request.nonce) (absBytes request.associated_data)
        (RegistrationRecordPrimitives.plaintextBytes request.plaintext) := by
  have projected : (.Some (ciphertext, tag), RegistrationWorldAgreement.project after) ∈ support
      ((RegistrationRecordPrimitives.implementation setup.source codec.frameWrite (.seal request)).run (RegistrationWorldAgreement.project before)) := by
    rw [← RegistrationWorldRecords.handler_project setup codec (.seal request) before, support_map]
    exact Set.mem_image_of_mem (Prod.map id RegistrationWorldAgreement.project) supported
  change (.Some (ciphertext, tag), RegistrationWorldAgreement.project after) ∈ support
    (pure (RegistrationRecordPrimitives.sealedBytes (some (setup.source.crypto.aeadSeal (absBytes request.key)
      (absBytes request.nonce) (absBytes request.associated_data) (RegistrationRecordPrimitives.plaintextBytes request.plaintext))),
      RegistrationWorldAgreement.project before) : ProbComp _) at projected
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at projected
  obtain ⟨ciphertextEq, tagEq⟩ := sealed _ ciphertext tag projected.1.symm
  exact Prod.ext ciphertextEq tagEq

/-- The actual seal request retains the selected material, full AD, and LE64 assigned identifier prefixed to the original application. -/
theorem request (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (trace : Trace implementation initial completed before after) :
    trace.aeadRequest.key = trace.aead.pending.seal.material.key.bytes ∧
      trace.aeadRequest.nonce = trace.aead.pending.seal.material.nonce.bytes ∧
      trace.aeadRequest.associated_data = initial.binding.associated_data ∧
      RegistrationRecordPrimitives.plaintextBytes trace.aeadRequest.plaintext =
        Pqxdh.LE64 initial.candidate.key_id.val ++ TranscriptAuthParts.absSlice initial.application := by
  obtain ⟨bound, boundRun, context, _sequence⟩ := RegistrationNativeServerRecordFields.context implementation initial completed before after trace
  obtain ⟨boundExpected, expectedRun, expectedBytes⟩ := registration_key_id_binding_abs initial.candidate.key_id
  have boundEq : boundExpected = bound := RustM.ok.inj (expectedRun.symm.trans boundRun)
  rw [boundEq] at expectedBytes
  have requested := trace.aeadRequested
  simp only [registration.ServerRecordAead.request, record_effects.SealAead.request,
    ratchet.concrete.SendSeal.impl.material, ratchet.concrete.SendSeal.impl.context,
    ratchet.RatchetMaterial.impl.key, ratchet.RatchetKey.as_bytes, ratchet.RatchetMaterial.impl.nonce,
    ratchet.RatchetNonce.as_bytes, context, serverRecordContext, record_effects.SealFrameContext.plaintext_request, bind_tc_ok] at requested
  have requestEq := RustM.ok.inj requested
  rw [← requestEq]
  exact ⟨rfl, rfl, rfl, by simpa only [RegistrationRecordPrimitives.plaintextBytes] using (congrArg
    (fun bytes => bytes ++ TranscriptAuthParts.absSlice initial.application) expectedBytes)⟩

end BeaconcryptCore.Computational.RegistrationNativeServerSealSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerSealSource.reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerSealSource.reply

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerSealSource.request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerSealSource.request
