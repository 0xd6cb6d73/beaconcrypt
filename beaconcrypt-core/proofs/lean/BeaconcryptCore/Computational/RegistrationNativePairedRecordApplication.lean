-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedRecordFields
import BeaconcryptCore.Computational.RegistrationNativeServerSealSource
import BeaconcryptCore.Computational.RegistrationNativeBeaconOpenSource
import BeaconcryptCore.Computational.RegistrationNativeBeaconCompletionFields

/-! Actual same-cache source record receipts establish complete AD281, sender, assigned ID and application agreement. The fixed source AEAD functional correctness is used only after deriving its actual key, nonce, AD and ciphertext/tag operands from the two source traces. No root-equality, partner-completion or KEM perfect-correctness premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedRecordApplication
open PqxdhServerAuthExperiment (Setup Codec Checks)
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.ProtocolComposition
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK Auxiliary Reader Encoded : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

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

/-- One actual successful source first-record pair agrees on complete AD, sender, allocated identifier and original application outside its actual shared-cache collision event. -/
theorem paired (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (codec : Codec Reader Encoded) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverBefore serverAfter : RegistrationWorldAgreement.State n Auxiliary)
    (serverTrace : RegistrationNativeServerRecordTrace.Trace (RegistrationWorldRecords.handler setup codec) serverInitial hashed serverBefore serverAfter)
    (capability : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon) (beaconBefore beaconAfter : Local n KemSK source)
    (beaconTrace : RegistrationNativeBeaconRecordTrace.Trace
      (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.record setup wire query)) phase completed beaconBefore beaconAfter)
    (metadata : BeaconPhaseMetadata capability phase)
    (genuine : RegistrationNativeBeaconCommitmentGenuine.Genuine phase)
    (cache : CtxRomAuth.CtxRO.QueryCache) (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverHashed : serverTrace.digestReply = .Some (RegistrationAuthenticationShared.digestArray serverDigest))
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
    RegistrationNativePairedRecordFields.paired setup codec serverInitial hashed serverBefore serverAfter serverTrace
      implementation capability phase completed beaconBefore beaconAfter beaconTrace metadata genuine cache serverDigest beaconDigest
      serverHashed serverCached beaconMatched beaconCached ciphertext collisionFree
  obtain ⟨body, tag, replied, written⟩ := RegistrationNativeServerRawSource.frame setup codec serverInitial hashed serverBefore serverAfter serverTrace serverDigest serverHashed
  have sealed := RegistrationNativeServerSealSource.reply setup codec serverTrace.aeadRequest serverTrace.second serverTrace.third body tag
    (by rw [← replied]; exact serverTrace.aeadCalled)
  obtain ⟨requestKey, requestNonce, requestAd, plaintextSpec⟩ := RegistrationNativeServerSealSource.request
    (RegistrationWorldRecords.handler setup codec) serverInitial hashed serverBefore serverAfter serverTrace
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
        (RegistrationNativeServerRecordFields.context (RegistrationWorldRecords.handler setup codec) serverInitial hashed serverBefore serverAfter serverTrace).choose_spec.2.1).trans requestAd.symm)
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

end BeaconcryptCore.Computational.RegistrationNativePairedRecordApplication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedRecordApplication.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedRecordApplication.paired
