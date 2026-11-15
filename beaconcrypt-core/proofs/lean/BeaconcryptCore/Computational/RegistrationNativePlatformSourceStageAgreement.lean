-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInitialKdf
import BeaconcryptCore.Computational.RegistrationNativeStagedRootOrFailure
import BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers

/-! Complete contents, actual reached initializer capabilities, and root-or-primitive-failure agreement are composed on one actual corrected Platform finish cut. The earlier Server stage is actual source record execution, not a completed-peer premise. The one local failure alternative retains the actual successful collector's private-row primitive sample. The earlier authentication pin and actual completion pin remain separate; no equality of independently charged pin calls is assumed. Global protected-issuance/family probability composition remains separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceStageAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower project)
variable {n : Nat} {E Platform ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]

/-- Complete staged source agreement retains the same actual authentication, agreement and record cuts. Root equality and complementary initializer streams are derived or an actual primitive recipient failure is retained. -/
theorem finish (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
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
    (prior : RegistrationNativeKemBirthInvariant.Holds setup before.1 before.2.2.pool)
    (prekey : owner.prekeyPublic = rootArray (setup.dh.publicKey owner.prekeyScalar))
    (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverReceipt : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token pin cache)
    (serverIdentity : packet.public.identity_key = rootArray (setup.joint.publicKeys created.seed).ed25519)
    (ephemeral : packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key)
    (kemCiphertext : packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext)
    (control : pqxdh.ServerState) (stagePin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability) (serverApplication : Slice U8)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverStarted : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control stagePin availability token.agreement serverApplication serverInitial)
    (issued : RegistrationNativePlatformSourceFinishContents.RecordCut (n := n) coins setup wire view failure allocation erased
      rawAllocation serializer serverInitial hashed cache)
    (extension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = packet.application) (collisionFree : ¬ CacheHasCollision cache) :
    ∃ adDigest aborted middle agreed recorded capability completed beaconInitial,
      original.aborted_state = .ok aborted ∧
      (.ok (.Ok ((RegistrationResponseExecutor.acceptedResponse original packet adDigest) : registration.AuthenticatedResponse)), middle) ∈ support
        ((lower setup checks representation created (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin original (.Some packet)))).run
            (RegistrationNativePlatformCompletionReceipt.consumed before index aborted)) ∧
      (.ok (.BeaconComplete capability), agreed) ∈ support ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon (RegistrationResponseExecutor.acceptedResponse original packet adDigest)))).run middle) ∧
      (.ok (.Ok completed), recorded) ∈ support ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run agreed) ∧
      registration.begin_beacon_completion capability = .ok beaconInitial ∧ beaconInitial.agreement = capability ∧
      RegistrationNativeCompletionContents.Outcome serverInitial (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability completed application ∧
      application = TranscriptAuthParts.absSlice serverApplication ∧
      ((token.agreement.root.bytes = capability.root.bytes ∧
        RegistrationNativeInitializedInitializers.Initializers crypto setup.source token.agreement capability serverInitial beaconInitial) ∨
        ∃ (beaconInput : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) (atRoot : Local n KemSK source),
          (some beaconInput, atRoot) ∈ support ((lower setup checks representation created
            (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
              (simulateQ (RegistrationBeaconAgreementRoot.callbacks (RegistrationResponseExecutor.acceptedResponse original packet adDigest))
                (PqxdhBeaconPhase2Preparation.collect () false true () [])))).run middle) ∧
          RegistrationNativeRecipientFailure.FailureAt setup middle.2.2.pool owner.kemHandle serverReceipt.root.collected beaconInput) := by
  obtain ⟨cutOwner, cutPending, cutOneTime, aborted, authenticated, middle,
      selected, cutPhase, moved, called, continued⟩ := RegistrationNativePlatformCompletionReceipt.cut setup checks representation created
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
  obtain ⟨generatedPool, owned⟩ := RegistrationNativeLowerGenerated.owner setup checks representation created before.1 owner
    (List.mem_of_getElem? found) _ (RegistrationNativePlatformCompletionReceipt.consumed before index aborted) middle _ prior called
  obtain ⟨capability, completed, agreed, recorded, agreementRun, recordRun, _beforeAgreement, afterRecord, returned⟩ :=
    RegistrationNativeCompletionRecordCache.platform setup checks representation created wire index owner oneTime (RegistrationResponseExecutor.acceptedResponse original packet adDigest) middle after application continued
  have compared := RegistrationNativeStagedRootOrFailure.root setup checks wire route representation created owner oneTime token pin cache serverReceipt
    (RegistrationResponseExecutor.acceptedResponse original packet adDigest)
    (by simpa only [RegistrationResponseExecutor.acceptedResponse, RegistrationResponseExecutor.completedBinding_pin] using coherent) capability middle agreed agreementRun generatedPool owned prekey serverIdentity ephemeral kemCiphertext
  obtain ⟨_input, _atRoot, _original, _collected, _fields, _prepared, literal, _stateEq⟩ :=
    RegistrationNativeBeaconAgreementInputReceipt.local_cut setup checks representation created owner oneTime (RegistrationResponseExecutor.acceptedResponse original packet adDigest)
    (by simpa only [RegistrationResponseExecutor.acceptedResponse, RegistrationResponseExecutor.completedBinding_pin] using coherent) capability middle agreed agreementRun
  have sameBinding : capability.binding = RegistrationResponseExecutor.completedBinding original adDigest := congrArg agreement.BeaconAgreement.binding literal
  have sameCiphertext : capability.application_ciphertext = packet.application := congrArg agreement.BeaconAgreement.application_ciphertext literal
  obtain ⟨serverBefore, serverAfter, serverRun, serverExtension⟩ := issued
  obtain ⟨ad, sender, assigned, plaintext, completedBinding⟩ := RegistrationNativePlatformPairedRecord.run coins setup checks wire representation created
    view correct failure allocation erased rawAllocation serializer serverInitial hashed serverBefore serverAfter capability completed agreed recorded cache
    serverRun serverExtension recordRun (afterRecord.trans extension) (ciphertext.trans sameCiphertext.symm) collisionFree
  have contents : RegistrationNativeCompletionContents.Outcome serverInitial (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability completed application :=
    ⟨sameBinding, sameCiphertext, ad.trans (congrArg session.CompletedRegistrationBinding.associated_data sameBinding), sender,
      assigned, returned.trans plaintext, by simpa only [sameBinding, RegistrationResponseExecutor.acceptedResponse] using completedBinding⟩
  obtain ⟨beaconInitial, _request, _atStep, _phase, started, sameInitial, _requested, _calledInitial, _resumed, _following⟩ :=
    RegistrationNativeInitialKdfReceipt.beacon_begin setup checks wire representation created capability completed agreed recorded recordRun
  obtain ⟨_serverDigest, _serverBinding, _completed, _same, serverApplicationEq, _started⟩ :=
    (RegistrationNativeServerBindingReceipt.initial_root control stagePin availability token.agreement serverApplication serverInitial serverStarted).2
  refine ⟨adDigest, aborted, middle, agreed, recorded, capability, completed, beaconInitial, moved, called, agreementRun, recordRun,
    started, sameInitial, contents, ?_, ?_⟩
  · exact contents.2.2.2.2.2.1.trans (congrArg TranscriptAuthParts.absSlice serverApplicationEq)
  · rcases compared with rootEq | failed
    · exact Or.inl ⟨rootEq, RegistrationNativeInitializerAgreement.kernels crypto setup.source control stagePin availability token.agreement capability
        serverApplication serverInitial beaconInitial serverStarted started rootEq⟩
    · exact Or.inr failed

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceStageAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceStageAgreement.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceStageAgreement.finish
