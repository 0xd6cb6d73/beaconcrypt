-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedRecord
import BeaconcryptCore.Computational.RegistrationNativeCompletionContents

/-! Complete corrected Platform Beacon finish agrees with an actually reached source allocator/AEAD/hash/raw-writer record cut. The actual mandatory authentication and copy/install suffix are retained, and both cuts use the same later shared cache. The earlier source cut may precede a failed response publication and does not assert a completed Server peer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceFinishContents
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativePlatformSourceSealTrace (joint)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]

/-- An actually reached source Platform first-record success and its concrete later shared-cache anchor. -/
def RecordCut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash) (cache : CtxRomAuth.CtxRO.QueryCache) : Prop :=
  ∃ before after : RegistrationServerRootCompiler.Local n × Platform,
    (.ok (.Ok hashed), after) ∈ support ((joint (RegistrationNativePlatformSourceSealTrace.record coins setup
      (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased (AdapterRecordRawBytes.helper rawAllocation serializer) initial)).run before) ∧
    after.1.world.1.primitive.2 ≤ cache

/-- Corrected complete Platform finish derives AD151, sender, assigned ID, exact application and populated binding from its mandatory response authentication and actual earlier source first-record cut. -/
theorem finish (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (owner : Owner source) (original : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes) (before after : Local n KemSK source)
    (found : before.1[index]? = some owner) (phase : owner.phase = .initSent original oneTime)
    (supported : (.ok (some application), after) ∈ support ((lower setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index (some packet))).run before))
    (coherent : original.control.expected_server_binding = original.binding.server_pin.binding)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash) (cache : CtxRomAuth.CtxRO.QueryCache)
    (issued : RecordCut (n := n) coins setup wire view failure allocation erased rawAllocation serializer serverInitial hashed cache)
    (extension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = packet.application) (collisionFree : ¬ CacheHasCollision cache) :
    ∃ adDigest capability completed, RegistrationNativeCompletionContents.Outcome serverInitial (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability completed application := by
  obtain ⟨cutOwner, cutPending, cutOneTime, aborted, authenticated, middle,
      selected, cutPhase, _moved, called, continued⟩ := RegistrationNativePlatformCompletionReceipt.cut setup checks representation created
    wire index (some packet) before after application supported
  have ownerEq : cutOwner = owner := Option.some.inj (selected.symm.trans found)
  subst cutOwner
  have phases : RegistrationNativeBeaconFrontend.Phase.initSent cutPending cutOneTime = .initSent original oneTime := cutPhase.symm.trans phase
  cases phases
  have projected : (.ok (.Ok authenticated), project middle) ∈ support
      ((RegistrationResponseExecutor.execute setup.source.crypto source.verify wire.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) original (.Some packet)).run
          (project (RegistrationNativePlatformCompletionReceipt.consumed before index aborted))) := by
    rw [RegistrationResponseExecutor.execute, ← RegistrationNativeResponseAuthentication.program setup checks representation created wire, support_map]
    exact Set.mem_image_of_mem (Prod.map id project) called
  obtain ⟨_digest, same, _verified, _receipts, _earlier, _cached⟩ := RegistrationResponseExecutor.accepted_receipt
    setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) original packet
    (project (RegistrationNativePlatformCompletionReceipt.consumed before index aborted)) (project middle) authenticated projected
  obtain ⟨adDigest, same⟩ := same
  subst authenticated
  obtain ⟨capability, completed, agreed, recorded, agreementRun, recordRun, _beforeAgreement, afterRecord, returned⟩ :=
    RegistrationNativeCompletionRecordCache.platform setup checks representation created wire index owner oneTime (RegistrationResponseExecutor.acceptedResponse original packet adDigest) middle after application continued
  obtain ⟨_input, _atRoot, _original, _collected, _fields, _prepared, literal, _stateEq⟩ :=
    RegistrationNativeBeaconAgreementInputReceipt.local_cut setup checks representation created owner oneTime (RegistrationResponseExecutor.acceptedResponse original packet adDigest)
    (by simpa only [RegistrationResponseExecutor.acceptedResponse, RegistrationResponseExecutor.completedBinding_pin] using coherent) capability middle agreed agreementRun
  have sameBinding : capability.binding = RegistrationResponseExecutor.completedBinding original adDigest := congrArg agreement.BeaconAgreement.binding literal
  have sameCiphertext : capability.application_ciphertext = packet.application := congrArg agreement.BeaconAgreement.application_ciphertext literal
  obtain ⟨serverBefore, serverAfter, serverRun, serverExtension⟩ := issued
  obtain ⟨ad, sender, assigned, plaintext, completedBinding⟩ := RegistrationNativePlatformPairedRecord.run coins setup checks wire representation created
    view correct failure allocation erased rawAllocation serializer serverInitial hashed serverBefore serverAfter capability completed agreed recorded cache
    serverRun serverExtension recordRun (afterRecord.trans extension) (ciphertext.trans sameCiphertext.symm) collisionFree
  refine ⟨adDigest, capability, completed, sameBinding, sameCiphertext, ?_, sender, assigned, returned.trans plaintext, ?_⟩
  · exact ad.trans (congrArg session.CompletedRegistrationBinding.associated_data sameBinding)
  · simpa only [sameBinding, RegistrationResponseExecutor.acceptedResponse] using completedBinding

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceFinishContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceFinishContents.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceFinishContents.finish
