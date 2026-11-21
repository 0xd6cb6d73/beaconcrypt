-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTraceAdapter
import BeaconcryptCore.Computational.RegistrationNativePairedRecordApplication

/-! Source-independent paired record contents consume actual successful trace operands, exact raw-writer bytes, actual source AEAD output and same-cache commitment receipts. This surface applies to the actual allocator/writer Platform trace projection without identifying that controller with the old World handler. Its concrete leaf inputs must come from the actual source cuts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedRecordSurface
open PqxdhServerAuthExperiment (Setup Checks)
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.CommitmentSurface
open BeaconcryptCore.Refinement.PqxdhSurface
open BeaconcryptCore.Refinement.ProtocolComposition
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Actual raw writer and same-cache receipts determine identical full source fields for arbitrary stateful Server/Beacon record interpreters. -/
theorem fields {SS BS : Type} (serverImplementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT SS ProbComp))
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverBefore serverAfter : SS)
    (serverTrace : RegistrationNativeServerRecordTrace.Trace serverImplementation serverInitial hashed serverBefore serverAfter)
    (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT BS ProbComp))
    (capability : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon) (beaconBefore beaconAfter : BS)
    (beaconTrace : RegistrationNativeBeaconRecordTrace.Trace implementation phase completed beaconBefore beaconAfter)
    (metadata : BeaconPhaseMetadata capability phase)
    (genuine : RegistrationNativeBeaconCommitmentGenuine.Genuine phase)
    (cache : CtxRomAuth.CtxRO.QueryCache) (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (body : Slice U8) (tag : Std.Array U8 16#usize)
    (written : TranscriptAuthParts.absSlice hashed.ciphertext = TranscriptAuthParts.absSlice body ++ absBytes tag ++ serverDigest.toList)
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
  obtain ⟨serverBody, serverTag, serverFields, _serverReply, serverKey, serverNonce, serverAd, serverSeq, serverSender, _tag, serverInput⟩ :=
    RegistrationNativeServerRawSource.fields serverImplementation serverInitial hashed serverBefore serverAfter serverTrace
  obtain ⟨beaconFields, beaconInput, beaconAd, beaconSeq, beaconSender, _beaconTag, supplied, key, nonce, ad, encrypted⟩ :=
    RegistrationNativeBeaconOpenFields.request implementation capability phase completed beaconBefore beaconAfter beaconTrace metadata genuine
  obtain ⟨bound, _boundRun, context, _sequence⟩ := RegistrationNativeServerRecordFields.context
    serverImplementation serverInitial hashed serverBefore serverAfter serverTrace
  have digestEq : beaconDigest = serverDigest := RegistrationNativePairedRecordFields.digest capability.application_ciphertext body tag beaconTrace.supplied
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


/-- Actual source AEAD correctness on those derived operands determines the original application and populated binding, for the real Platform Server callback surface. -/
theorem application {SS : Type} (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (serverImplementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT SS ProbComp)) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverBefore serverAfter : SS)
    (serverTrace : RegistrationNativeServerRecordTrace.Trace serverImplementation serverInitial hashed serverBefore serverAfter)
    (capability : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon) (beaconBefore beaconAfter : Local n KemSK source)
    (beaconTrace : RegistrationNativeBeaconRecordTrace.Trace
      (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire query)) phase completed beaconBefore beaconAfter)
    (metadata : BeaconPhaseMetadata capability phase)
    (genuine : RegistrationNativeBeaconCommitmentGenuine.Genuine phase)
    (cache : CtxRomAuth.CtxRO.QueryCache) (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (body : Slice U8) (tag : Std.Array U8 16#usize)
    (written : TranscriptAuthParts.absSlice hashed.ciphertext = TranscriptAuthParts.absSlice body ++ absBytes tag ++ serverDigest.toList)
    (sealed : (TranscriptAuthParts.absSlice body, absBytes tag) =
      setup.source.crypto.aeadSeal (absBytes serverTrace.aeadRequest.key) (absBytes serverTrace.aeadRequest.nonce)
        (absBytes serverTrace.aeadRequest.associated_data) (RegistrationRecordPrimitives.plaintextBytes serverTrace.aeadRequest.plaintext))
    (serverCached : cache ((), absBytes serverTrace.transcript.bytes) = some serverDigest)
    (beaconMatched : absBytes beaconTrace.supplied = beaconDigest.toList)
    (beaconCached : cache ((), absBytes beaconTrace.transcript.bytes) = some beaconDigest)
    (ciphertext : hashed.ciphertext = capability.application_ciphertext)
    (collisionFree : ¬ CacheHasCollision cache) :
    serverInitial.binding.associated_data = capability.binding.associated_data ∧
      serverInitial.candidate.server_identity_key_id = capability.candidate.server_binding.identity_key_id ∧
      serverInitial.candidate.key_id = capability.candidate.assigned_key_id ∧
      TranscriptAuthParts.absSlice completed.application = TranscriptAuthParts.absSlice serverInitial.application ∧
      completed.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        capability.binding serverInitial.candidate.key_id := by
  let implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT (Local n KemSK source) ProbComp) := fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire query)
  obtain ⟨fields, _serverEncoded, _beaconEncoded, serverAd, beaconAd, _sequence, serverSender, beaconSender, key, nonce, ad, encrypted⟩ :=
    fields serverImplementation serverInitial hashed serverBefore serverAfter serverTrace
      implementation capability phase completed beaconBefore beaconAfter beaconTrace metadata genuine cache serverDigest beaconDigest
      body tag written serverCached beaconMatched beaconCached ciphertext collisionFree
  obtain ⟨requestKey, requestNonce, requestAd, plaintextSpec⟩ := RegistrationNativeServerSealSource.request
    serverImplementation serverInitial hashed serverBefore serverAfter serverTrace
  have bodyEq : TranscriptAuthParts.absSlice beaconTrace.aeadRequest.ciphertext = TranscriptAuthParts.absSlice body ++ absBytes tag := by
    have sliced : TranscriptAuthParts.absSlice beaconTrace.aeadRequest.ciphertext =
        (TranscriptAuthParts.absSlice hashed.ciphertext).take ((TranscriptAuthParts.absSlice hashed.ciphertext).length - 64) := by
      simpa only [TranscriptAuthParts.absSlice, List.map_take, List.length_map] using congrArg (List.map absByte) encrypted
    rw [written] at sliced
    rw [List.length_append, List.Vector.toList_length, Nat.add_sub_cancel_right, List.take_left] at sliced
    exact sliced
  have sourceOpen : RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput beaconTrace.aeadRequest) =
      some (RegistrationRecordPrimitives.plaintextBytes serverTrace.aeadRequest.plaintext) := by
    have openKey : beaconTrace.aeadRequest.key = serverTrace.aeadRequest.key := key.trans requestKey.symm
    have openNonce : beaconTrace.aeadRequest.nonce = serverTrace.aeadRequest.nonce := nonce.trans requestNonce.symm
    have openAd : beaconTrace.aeadRequest.associated_data = serverTrace.aeadRequest.associated_data :=
      ad.trans ((congrArg record_effects.SealFrameContext.associated_data
        (RegistrationNativeServerRecordFields.context serverImplementation serverInitial hashed serverBefore serverAfter serverTrace).choose_spec.2.1).trans requestAd.symm)
    change RawCtxSourceOpen.baseOpen setup.source.crypto ⟨_, _, _, _⟩ = _
    rw [bodyEq, openKey, openNonce, openAd, RawCtxSourceOpen.baseOpen_combined setup.source.crypto _ _ _ _ _ (by simp)]
    have sealedBody := congrArg Prod.fst sealed
    have sealedTag := congrArg Prod.snd sealed
    dsimp only [Prod.fst] at sealedBody
    dsimp only [Prod.snd] at sealedTag
    rw [sealedBody, sealedTag]
    exact setup.source.crypto.aead_open_seal _ _ _ _
  have actualOpen := RegistrationNativeBeaconOpenSource.reply setup checks wire representation created beaconTrace.aeadRequest
    beaconTrace.afterHash beaconAfter beaconTrace.openReply beaconTrace.aeadCalled
  rw [sourceOpen] at actualOpen
  obtain ⟨plaintext, plainReply, _nonempty, assigned, completedBinding, completedApp⟩ :=
    RegistrationNativeBeaconCompletionFields.completed implementation capability phase completed beaconBefore beaconAfter beaconTrace metadata
  have plainBytes := opened _ plaintext (actualOpen.symm.trans plainReply)
  have prefixEq : Pqxdh.LE64 serverInitial.candidate.key_id.val = Pqxdh.LE64 capability.candidate.assigned_key_id.val := by
    have checked : (TranscriptAuthParts.absSlice plaintext).take 8 = Pqxdh.LE64 capability.candidate.assigned_key_id.val := by
      simpa only [TranscriptAuthParts.absSlice, List.map_take] using assigned
    rw [plainBytes, plaintextSpec] at checked
    simpa only [← Pqxdh.LE64_length serverInitial.candidate.key_id.val, List.take_left] using checked
  have assignedEq : serverInitial.candidate.key_id = capability.candidate.assigned_key_id :=
    UScalar.eq_of_val_eq (Pqxdh.LE64_inj serverInitial.candidate.key_id.bv.isLt capability.candidate.assigned_key_id.bv.isLt prefixEq)
  refine ⟨serverAd.symm.trans beaconAd, serverSender.symm.trans beaconSender, assignedEq, ?_, ?_⟩
  · rw [completedApp]
    change List.map absByte (plaintext.val.drop 8) = _
    rw [List.map_drop]
    change (TranscriptAuthParts.absSlice plaintext).drop 8 = _
    rw [plainBytes, plaintextSpec]
    rw [← Pqxdh.LE64_length serverInitial.candidate.key_id.val, List.drop_append_length]
  · exact completedBinding.trans (congrArg (BeaconcryptCore.Refinement.RegistrationPublication.completedBinding capability.binding) assignedEq.symm)


end BeaconcryptCore.Computational.RegistrationNativePairedRecordSurface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedRecordSurface.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedRecordSurface.fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedRecordSurface.application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedRecordSurface.application
