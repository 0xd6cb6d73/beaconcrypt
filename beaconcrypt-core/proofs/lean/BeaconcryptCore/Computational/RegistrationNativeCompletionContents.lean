-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCompletionRecordCache
import BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt

/-! The complete original and corrected assigned-ID Beacon finish continuations retain the local source contents agreement and its actual cache suffix. The earlier issued Server record remains an actual source cut, distinct from completed Server peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCompletionContents
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Contents of one actual post-authentication cut, including the exact populated completion binding. -/
def Outcome (serverInitial : registration.ServerInitialKdf) (authenticated : registration.AuthenticatedResponse)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon) (application : Pqxdh.Bytes) : Prop :=
  capability.binding = authenticated.binding ∧ capability.application_ciphertext = authenticated.packet.application ∧
    serverInitial.binding.associated_data = authenticated.binding.associated_data ∧
    serverInitial.candidate.server_identity_key_id = capability.candidate.server_binding.identity_key_id ∧
    serverInitial.candidate.key_id = capability.candidate.assigned_key_id ∧
    application = TranscriptAuthParts.absSlice serverInitial.application ∧
    completed.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
      authenticated.binding serverInitial.candidate.key_id

/-- Actual agreement/record cuts discharge the complete local source contents outcome. -/
theorem from_cut (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon)
    (before agreed recorded : Local n KemSK source) (cache : CtxRomAuth.CtxRO.QueryCache) (application : Pqxdh.Bytes)
    (issued : RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) serverInitial hashed cache)
    (agreementRun : (.ok (.BeaconComplete capability), agreed) ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before))
    (recordRun : (.ok (.Ok completed), recorded) ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run agreed))
    (extension : RegistrationNativeWorldCache.cache recorded.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = authenticated.packet.application)
    (returned : application = TranscriptAuthParts.absSlice completed.application)
    (collisionFree : ¬ CacheHasCollision cache) : Outcome serverInitial authenticated capability completed application := by
  obtain ⟨_input, _atRoot, _original, _collected, _fields, _prepared, literal, _stateEq⟩ :=
    RegistrationNativeBeaconAgreementInputReceipt.local_cut setup checks representation created owner oneTime authenticated coherent capability before agreed agreementRun
  have sameBinding : capability.binding = authenticated.binding := congrArg agreement.BeaconAgreement.binding literal
  have sameCiphertext : capability.application_ciphertext = authenticated.packet.application := congrArg agreement.BeaconAgreement.application_ciphertext literal
  obtain ⟨ad, sender, assigned, plaintext, completedBinding⟩ := RegistrationNativePairedRecordContents.run setup checks wire representation created
    serverInitial hashed capability completed agreed recorded cache issued recordRun extension (ciphertext.trans sameCiphertext.symm) collisionFree
  refine ⟨sameBinding, sameCiphertext, ?_, sender, assigned, returned.trans plaintext, ?_⟩
  · exact ad.trans (congrArg session.CompletedRegistrationBinding.associated_data sameBinding)
  · simpa only [sameBinding] using completedBinding

/-- Complete original post-authentication finish retains this contents outcome through its actual installation and phase-update suffix. -/
theorem legacy (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (before after : Local n KemSK source) (cache : CtxRomAuth.CtxRO.QueryCache) (application : Pqxdh.Bytes)
    (issued : RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) serverInitial hashed cache)
    (supported : (.ok (some application), after) ∈ support ((lower setup checks representation created
      (RegistrationNativeResponseFinish.afterAuthentication setup wire index owner oneTime authenticated)).run before))
    (extension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = authenticated.packet.application) (collisionFree : ¬ CacheHasCollision cache) :
    ∃ capability completed, Outcome serverInitial authenticated capability completed application := by
  obtain ⟨capability, completed, agreed, recorded, agreementRun, recordRun, _beforeAgreement, afterRecord, returned⟩ :=
    RegistrationNativeCompletionRecordCache.legacy setup checks representation created wire index owner oneTime authenticated before after application supported
  exact ⟨capability, completed, from_cut setup checks wire representation created owner oneTime authenticated coherent serverInitial hashed
    capability completed before agreed recorded cache application issued agreementRun recordRun (afterRecord.trans extension) ciphertext returned collisionFree⟩

/-- Complete corrected assigned-ID platform finish retains this same source contents outcome through its actual copy/install/phase-update suffix. -/
theorem platform (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (before after : Local n KemSK source) (cache : CtxRomAuth.CtxRO.QueryCache) (application : Pqxdh.Bytes)
    (issued : RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) serverInitial hashed cache)
    (supported : (.ok (some application), after) ∈ support ((lower setup checks representation created
      (RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index owner oneTime authenticated)).run before))
    (extension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = authenticated.packet.application) (collisionFree : ¬ CacheHasCollision cache) :
    ∃ capability completed, Outcome serverInitial authenticated capability completed application := by
  obtain ⟨capability, completed, agreed, recorded, agreementRun, recordRun, _beforeAgreement, afterRecord, returned⟩ :=
    RegistrationNativeCompletionRecordCache.platform setup checks representation created wire index owner oneTime authenticated before after application supported
  exact ⟨capability, completed, from_cut setup checks wire representation created owner oneTime authenticated coherent serverInitial hashed
    capability completed before agreed recorded cache application issued agreementRun recordRun (afterRecord.trans extension) ciphertext returned collisionFree⟩

end BeaconcryptCore.Computational.RegistrationNativeCompletionContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionContents.from_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionContents.from_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionContents.legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionContents.legacy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionContents.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionContents.platform
