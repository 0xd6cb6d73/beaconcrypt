-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldStageCache
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishRootReceipt

/-! Actual Server and Beacon record commitment callbacks retain their exact single shared-cache query and digest. Marker updates are retained and no source cache is reset or replaced by an unrelated reply. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeResponseAuthentication (lower_bind)
variable {n : Nat} {ι KemSK Auxiliary Reader Encoded : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The actual instrumented World commitment hash has its exact returned digest and final-cache receipt. -/
theorem world (setup : Setup base KemSK) (codec : Codec Reader Encoded)
    (transcript : commitment.CommitmentTranscript) (before after : RegistrationWorldAgreement.State n Auxiliary)
    (answer : RegistrationRecordPrimitives.Spec.Range (.hash transcript))
    (supported : (answer, after) ∈ support ((RegistrationWorldRecords.handler setup codec (.hash transcript)).run before)) :
    ∃ digest, answer = .Some (RegistrationAuthenticationShared.digestArray digest) ∧
      before.world.1.primitive.2 ≤ after.world.1.primitive.2 ∧
      after.world.1.primitive.2 ((), absBytes transcript.bytes) = some digest := by
  have projected : (answer, RegistrationWorldAgreement.project after) ∈ support
      ((RegistrationRecordPrimitives.implementation setup.source codec.frameWrite (.hash transcript)).run (RegistrationWorldAgreement.project before)) := by
    rw [← RegistrationWorldRecords.handler_project setup codec (.hash transcript) before, support_map]
    exact Set.mem_image_of_mem (Prod.map id RegistrationWorldAgreement.project) supported
  rw [RegistrationRecordPrimitives.hash_exact, support_map] at projected
  obtain ⟨inner, called, same⟩ := projected
  have replyEq : answer = .Some (RegistrationAuthenticationShared.digestArray inner.1) := (congrArg Prod.fst same).symm
  have cacheEq : after.world.1.primitive.2 = inner.2 := (congrArg (fun value => value.2.2) same).symm
  have cached := MldsaSharedAuthentication.query_cached (absBytes transcript.bytes) before.world.1.primitive.2 inner called
  exact ⟨inner.1, replyEq, cacheEq ▸ cached.1, cacheEq ▸ cached.2⟩

/-- The record marker precedes the identical actual authentication-style hash callback in the same native interpreter. -/
theorem record_hash (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (transcript : commitment.CommitmentTranscript) :
    RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire (.hash transcript) =
      (do RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall (.hash transcript)]}
          RegistrationNativeBeaconFrontend.authentication setup source (.hash (.Single (Std.Array.to_slice transcript.bytes)))) := rfl

/-- The actual native Beacon commitment query returns its literal digest in the same reached shared cache. -/
theorem beacon (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (transcript : commitment.CommitmentTranscript) (before after : Local n KemSK source)
    (answer : RegistrationRecordPrimitives.Spec.Range (.hash transcript))
    (supported : (answer, after) ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.record setup wire (.hash transcript))).run before)) :
    ∃ digest, answer = .Some (RegistrationAuthenticationShared.digestArray digest) ∧
      RegistrationNativeWorldCache.cache before.2.2 ≤ RegistrationNativeWorldCache.cache after.2.2 ∧
      RegistrationNativeWorldCache.cache after.2.2 ((), absBytes transcript.bytes) = some digest := by
  have extension := RegistrationNativeWorldCache.localProgram setup checks representation created _ before (answer, after) supported
  rw [record_hash, lower_bind] at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨ignored, current⟩, _updated, called⟩ := supported
  have projected : (answer, project after) ∈ support
      ((RegistrationAuthenticationShared.implementation setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
        (.hash (.Single (Std.Array.to_slice transcript.bytes)))).run (project current)) := by
    rw [← RegistrationNativeResponseAuthentication.query setup checks representation created wire (.hash (.Single (Std.Array.to_slice transcript.bytes))) current, support_map]
    exact Set.mem_image_of_mem (Prod.map id project) called
  obtain ⟨digest, replyEq, _receipts, _cachedEarlier, cached⟩ := RegistrationAuthenticationShared.hash_reply_cached setup.source.crypto source.verify wire.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) (.Single (Std.Array.to_slice transcript.bytes)) (project current) (project after) answer projected
  refine ⟨digest, replyEq, extension, ?_⟩
  simpa only [BeaconcryptCore.Refinement.RegistrationInputs.hashBytes, TranscriptAuthParts.absSlice, Std.Array.to_slice, absBytes, project, RegistrationNativeWorldCache.cache] using cached

end BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt.record_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt.record_hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt.beacon
