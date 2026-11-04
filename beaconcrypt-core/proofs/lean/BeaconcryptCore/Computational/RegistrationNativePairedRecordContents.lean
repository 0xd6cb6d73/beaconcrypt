-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedRecordApplication

/-! Source cuts alone supply all actual record traces, metadata, source-built transcripts and same-cache commitment receipts required for complete first-record contents agreement. No supplied transcript-field equality, root equality, sampled reply equality or perfect recipient-correctness premise is needed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedRecordContents
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Actual issued Server record and successful native Beacon first-record completion on the same response bytes agree on complete AD, sender, assigned ID, application and populated binding outside their actual later shared-cache collision event. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon)
    (before after : Local n KemSK source) (cache : CtxRomAuth.CtxRO.QueryCache)
    (issued : RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) serverInitial hashed cache)
    (supported : (.ok (.Ok completed), after) ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run before))
    (extension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = capability.application_ciphertext)
    (collisionFree : ¬ CacheHasCollision cache) :
    serverInitial.binding.associated_data = capability.binding.associated_data ∧
      serverInitial.candidate.server_identity_key_id = capability.candidate.server_binding.identity_key_id ∧
      serverInitial.candidate.key_id = capability.candidate.assigned_key_id ∧
      TranscriptAuthParts.absSlice completed.application = TranscriptAuthParts.absSlice serverInitial.application ∧
      completed.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        capability.binding serverInitial.candidate.key_id := by
  obtain ⟨serverBefore, serverAfter, serverTrace, serverDigest, serverHashed, serverCached⟩ :=
    RegistrationNativeServerRecordHashSource.issued setup (RegistrationNativeWire.ledgerCodec wire) serverInitial hashed cache issued
  obtain ⟨initial, request, atStep, phase, beaconTrace, beaconDigest, _started, sameAgreement, _requested, resumed,
      _hashed, matched, cached⟩ :=
    RegistrationNativeBeaconRecordHashSource.run setup checks wire representation created capability completed before after cache supported extension
  have metadata := RegistrationNativeBeaconRecordFields.initial initial _ phase resumed
  rw [sameAgreement] at metadata
  have genuine := RegistrationNativeBeaconCommitmentGenuine.initial initial _ phase resumed
  exact RegistrationNativePairedRecordApplication.paired setup checks wire (RegistrationNativeWire.ledgerCodec wire) representation created
    serverInitial hashed serverBefore serverAfter serverTrace capability phase completed atStep after beaconTrace metadata genuine cache
    serverDigest beaconDigest serverHashed serverCached matched cached ciphertext collisionFree

end BeaconcryptCore.Computational.RegistrationNativePairedRecordContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedRecordContents.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedRecordContents.run
