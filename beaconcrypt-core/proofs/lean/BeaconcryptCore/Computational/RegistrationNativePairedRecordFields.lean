-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerRawSource
import BeaconcryptCore.Computational.RegistrationNativeBeaconOpenFields

/-! Actual Server raw writer and Beacon payload slicing determine the same supplied commitment digest. Their actual same-cache receipts then determine all six source commitment fields outside the one shared-cache collision event. No root equality or private KEM correctness premise is needed for this content-binding statement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedRecordFields
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.CommitmentSurface
open BeaconcryptCore.Refinement.PqxdhSurface
variable {n : Nat} {ι KemSK Auxiliary Reader Encoded S : Type} {base : OracleSpec ι}

/-- The supplied digest is determined by the source writer's actual complete raw frame. -/
theorem digest (payload body : Slice U8) (tag : Std.Array U8 16#usize) (supplied : Std.Array U8 64#usize)
    (expected actual : CtxRomAuth.CtxDigest)
    (written : TranscriptAuthParts.absSlice payload = TranscriptAuthParts.absSlice body ++ absBytes tag ++ expected.toList)
    (sliced : supplied.val = payload.val.drop (payload.val.length - 64))
    (matched : absBytes supplied = actual.toList) : actual = expected := by
  have suppliedTail : absBytes supplied = (TranscriptAuthParts.absSlice payload).drop ((TranscriptAuthParts.absSlice payload).length - 64) := by
    simpa only [absBytes, TranscriptAuthParts.absSlice, List.map_drop, List.length_map] using congrArg (List.map absByte) sliced
  have tail : (TranscriptAuthParts.absSlice payload).drop ((TranscriptAuthParts.absSlice payload).length - 64) = expected.toList := by
    rw [written]
    rw [List.length_append, List.Vector.toList_length, Nat.add_sub_cancel_right, List.drop_append_length]
  exact List.Vector.toList_injective (matched.symm.trans (suppliedTail.trans tail))

/-- Both actual source commitment transcripts and the final open request have one identical full field tuple outside the literal shared-cache collision event. -/
theorem paired (setup : Setup base KemSK) (codec : Codec Reader Encoded)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverBefore serverAfter : RegistrationWorldAgreement.State n Auxiliary)
    (serverTrace : RegistrationNativeServerRecordTrace.Trace (RegistrationWorldRecords.handler setup codec) serverInitial hashed serverBefore serverAfter)
    (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (capability : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon) (beaconBefore beaconAfter : S)
    (beaconTrace : RegistrationNativeBeaconRecordTrace.Trace implementation phase completed beaconBefore beaconAfter)
    (metadata : BeaconPhaseMetadata capability phase)
    (genuine : RegistrationNativeBeaconCommitmentGenuine.Genuine phase)
    (cache : CtxRomAuth.CtxRO.QueryCache) (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverHashed : serverTrace.digestReply = .Some (RegistrationAuthenticationShared.digestArray serverDigest))
    (serverCached : cache ((), absBytes serverTrace.transcript.bytes) = some serverDigest)
    (beaconMatched : absBytes beaconTrace.supplied = beaconDigest.toList)
    (beaconCached : cache ((), absBytes beaconTrace.transcript.bytes) = some beaconDigest)
    (ciphertext : hashed.ciphertext = capability.application_ciphertext)
    (collisionFree : ¬ CacheHasCollision cache) :
    ∃ fields : Fields, serverTrace.transcript.bytes = productionInput fields ∧ beaconTrace.transcript.bytes = productionInput fields ∧
      fields.associatedData = serverInitial.binding.associated_data ∧ fields.associatedData = capability.binding.associated_data ∧
      fields.sequence = 1#u64 ∧ fields.senderId = serverInitial.candidate.server_identity_key_id ∧
      fields.senderId = capability.candidate.server_binding.identity_key_id ∧
      beaconTrace.aeadRequest.key = serverTrace.aead.pending.seal.material.key.bytes ∧
      beaconTrace.aeadRequest.nonce = serverTrace.aead.pending.seal.material.nonce.bytes ∧
      beaconTrace.aeadRequest.associated_data = serverTrace.aead.pending.seal.context.associated_data ∧
      beaconTrace.aeadRequest.ciphertext.val = hashed.ciphertext.val.take (hashed.ciphertext.val.length - 64) := by
  obtain ⟨body, tag, _sealed, written⟩ := RegistrationNativeServerRawSource.frame setup codec serverInitial hashed serverBefore serverAfter serverTrace serverDigest serverHashed
  obtain ⟨serverBody, serverTag, serverFields, _serverReply, serverKey, serverNonce, serverAd, serverSeq, serverSender, _tag, serverInput⟩ :=
    RegistrationNativeServerRawSource.fields (RegistrationWorldRecords.handler setup codec) serverInitial hashed serverBefore serverAfter serverTrace
  obtain ⟨beaconFields, beaconInput, beaconAd, beaconSeq, beaconSender, _beaconTag, supplied, key, nonce, ad, encrypted⟩ :=
    RegistrationNativeBeaconOpenFields.request implementation capability phase completed beaconBefore beaconAfter beaconTrace metadata genuine
  obtain ⟨bound, _boundRun, context, _sequence⟩ := RegistrationNativeServerRecordFields.context
    (RegistrationWorldRecords.handler setup codec) serverInitial hashed serverBefore serverAfter serverTrace
  have digestEq : beaconDigest = serverDigest := digest capability.application_ciphertext body tag beaconTrace.supplied
    serverDigest beaconDigest (ciphertext ▸ written) supplied beaconMatched
  have sameQueries := cache_lookup_eq_of_noCollision collisionFree serverCached ⟨beaconDigest, beaconCached, by rw [digestEq]⟩
  have sameBytes : serverTrace.transcript.bytes = beaconTrace.transcript.bytes := bytes_eq_of_abs_eq (congrArg Prod.snd sameQueries)
  have fieldsEq : beaconFields = serverFields := production_commitment_input_is_injective
    (beaconInput.symm.trans (sameBytes.symm.trans serverInput))
  refine ⟨serverFields, serverInput, beaconInput.trans (congrArg productionInput fieldsEq), serverAd,
    fieldsEq ▸ beaconAd, serverSeq, serverSender, fieldsEq ▸ beaconSender, ?_, ?_, ?_, ?_⟩
  · exact key.trans ((congrArg Fields.key fieldsEq).trans serverKey)
  · exact nonce.trans ((congrArg Fields.nonce fieldsEq).trans serverNonce)
  · exact ad.trans ((congrArg Fields.associatedData fieldsEq).trans
      (serverAd.trans (congrArg record_effects.SealFrameContext.associated_data context).symm))
  · exact ciphertext ▸ encrypted

end BeaconcryptCore.Computational.RegistrationNativePairedRecordFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedRecordFields.digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedRecordFields.digest

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedRecordFields.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedRecordFields.paired
