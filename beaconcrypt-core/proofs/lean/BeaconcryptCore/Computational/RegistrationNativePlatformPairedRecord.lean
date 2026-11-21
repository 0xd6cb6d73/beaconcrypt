-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformSealValues
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePairedRecordSurface

/-! Actual source Platform first-record success and the unchanged Beacon first-record core agree on complete AD281, sender, assigned identifier, original application and populated binding outside their actual common cache-collision event. Every trace, raw writer byte equation, native AEAD operand and hash receipt is derived from the actual source callbacks, retaining external allocation state. No root-equality, KEM perfect-correctness, codec-law or completed Server installation premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedRecord
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativePlatformSourceSealTrace (joint)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]

/-- One actual source Platform record and one actual successful Beacon record on the same response bytes derive full contents agreement. -/
theorem run (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverBefore serverAfter : RegistrationServerRootCompiler.Local n × Platform)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon) (before after : Local n KemSK source)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverRun : (.ok (.Ok hashed), serverAfter) ∈ support ((joint (RegistrationNativePlatformSourceSealTrace.record coins setup
      (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased (AdapterRecordRawBytes.helper rawAllocation serializer) serverInitial)).run serverBefore))
    (serverExtension : serverAfter.1.world.1.primitive.2 ≤ cache)
    (beaconRun : (.ok (.Ok completed), after) ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run before))
    (beaconExtension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = capability.application_ciphertext) (collisionFree : ¬ CacheHasCollision cache) :
    serverInitial.binding.associated_data = capability.binding.associated_data ∧
      serverInitial.candidate.server_identity_key_id = capability.candidate.server_binding.identity_key_id ∧
      serverInitial.candidate.key_id = capability.candidate.assigned_key_id ∧
      TranscriptAuthParts.absSlice completed.application = TranscriptAuthParts.absSlice serverInitial.application ∧
      completed.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        capability.binding serverInitial.candidate.key_id := by
  obtain ⟨actual⟩ := RegistrationNativePlatformSourceSealTrace.run coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation
    erased (AdapterRecordRawBytes.helper rawAllocation serializer) serverInitial hashed serverBefore serverAfter serverRun
  let proxy := RegistrationNativePlatformRecordProjection.project _ _ _ _ serverInitial hashed serverBefore serverAfter actual
  have hashRun := (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mp actual.hashCalled
  obtain ⟨_replaced, _oldHash, serverDigest, serverHashed, _cacheExtension, cached⟩ := RegistrationNativePlatformHashReceipt.source coins setup
    (RegistrationNativeWire.ledgerCodec wire) erased actual.transcript actual.digestReply actual.erased actual.third.1 actual.fourth.1 actual.third.2 actual.fourth.2 hashRun
  obtain ⟨body, tag, replied, written, cacheEq⟩ := RegistrationNativePlatformRawFrame.frame coins setup (RegistrationNativeWire.ledgerCodec wire)
    view failure allocation erased rawAllocation serializer serverInitial hashed serverBefore serverAfter actual serverDigest serverHashed
  have sealedRun := actual.aeadCalled
  rw [replied] at sealedRun
  have nestedSeal := (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mp sealedRun
  have sealed := RegistrationNativePlatformSealValues.sealing coins setup (RegistrationNativeWire.ledgerCodec wire) view correct failure allocation
    actual.aeadRequest body tag actual.second.1 actual.third.1 actual.second.2 actual.third.2 nestedSeal
  have serverCached : cache ((), absBytes actual.transcript.bytes) = some serverDigest := by
    apply serverExtension
    rw [← cacheEq]
    exact cached
  obtain ⟨initial, request, atStep, phase, beaconTrace, beaconDigest, _started, sameAgreement, _requested, resumed,
      _hashed, matched, beaconCached⟩ := RegistrationNativeBeaconRecordHashSource.run setup checks wire representation created
    capability completed before after cache beaconRun beaconExtension
  have metadata := RegistrationNativeBeaconRecordFields.initial initial _ phase resumed
  rw [sameAgreement] at metadata
  have genuine := RegistrationNativeBeaconCommitmentGenuine.initial initial _ phase resumed
  exact RegistrationNativePairedRecordSurface.application setup checks wire _ representation created serverInitial hashed serverBefore serverAfter proxy
    capability phase completed atStep after beaconTrace metadata genuine cache serverDigest beaconDigest body tag written sealed
    serverCached matched beaconCached ciphertext collisionFree

end BeaconcryptCore.Computational.RegistrationNativePlatformPairedRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedRecord.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedRecord.run
