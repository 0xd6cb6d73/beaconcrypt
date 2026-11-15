-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLoggedSourceStageAgreement
import BeaconcryptCore.Computational.RegistrationNativeLoggedStagedRootAgreement
import BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence
import BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers

/-! Given actual source agreement and first-record cuts determine their own root and initializer contents. The initializer and completed record are fixed inputs, never compatible existential witnesses chosen after an erasure. Failure is the same initialized finite-recipient marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementGivenCut
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower project)
variable {n count : Nat} {Value : Type} {E Platform ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]

theorem given_cut (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (owner : Owner source) (original : registration.BeaconPending) {adDigest : CtxRomAuth.CtxDigest} (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet :registration.ResponsePacket) (application :Pqxdh.Bytes)
    (middle agreed recorded :Local n KemSK source)
    (capability :agreement.BeaconAgreement) (completed :registration.CompletedBeacon)
    (beaconInitial :registration.BeaconInitialKdf)
    (agreementRun :(.ok (.BeaconComplete capability),agreed)∈support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
          (RegistrationAgreementExecutor.beacon (RegistrationResponseExecutor.acceptedResponse original packet adDigest)))).run middle))
    (recordRun :(.ok (.Ok completed),recorded)∈support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire)
          (RegistrationBeaconRecordExecutor.fromInitial beaconInitial))).run agreed))
    (started :registration.begin_beacon_completion capability=.ok beaconInitial)
    (returned :application=TranscriptAuthParts.absSlice completed.application)
    (coherent : original.control.expected_server_binding = original.binding.server_pin.binding)
    (prekey : owner.prekeyPublic = rootArray (setup.dh.publicKey owner.prekeyScalar))
    (work : OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) Value)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK Value count)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (sampled : result ∈ support (RegistrationNativeKemRecipientLogSource.experiment setup functional work count))
    (initPacket : registration.InitPacket) (initAuth : registration.AuthenticatedInit)
    (serverBefore serverAfter : RegistrationNativeKemServerState.State n source) (accepted : agreement.ServerAgreement)
    (receipt : RegistrationNativeKemTracedServerSource.Receipt setup checks representation created initPacket initAuth serverBefore serverAfter accepted result.2.1.1.2)
    (token : peer.ConsumedRegistration) (tokenEq : token.agreement = accepted)
    (matched : initAuth.registration = {
      beacon_identity_public_key := rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
      beacon_prekey_public_key := owner.prekeyPublic,
      beacon_one_time_public_key := rootArray (setup.dh.publicKey oneTime),
      beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic })
    (target : Fin count) (row : middle.2.2.pool.keys[owner.kemHandle]? = some (result.1 target).1)
    (publicKey : (result.1 target).1.1 = owner.kemPublic)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverIdentity : packet.public.identity_key = rootArray (setup.joint.publicKeys created.seed).ed25519)
    (ephemeral : packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key)
    (kemCiphertext : packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext)
    (control : pqxdh.ServerState) (stagePin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability) (serverApplication : Slice U8)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverStarted : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control stagePin availability token.agreement serverApplication serverInitial)
    (issued : RegistrationNativePlatformSourceFinishContents.RecordCut (n := n) coins setup wire view failure allocation erased
      rawAllocation serializer serverInitial hashed cache)
    (extension : RegistrationNativeWorldCache.cache recorded.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = packet.application) (collisionFree : ¬ CacheHasCollision cache) :
    RegistrationNativeCompletionContents.Outcome serverInitial (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability completed application ∧
    application=TranscriptAuthParts.absSlice serverApplication ∧
    ((token.agreement.root.bytes=capability.root.bytes ∧
      RegistrationNativeInitializedInitializers.Initializers crypto setup.source token.agreement capability serverInitial beaconInitial) ∨result.2.2=true) := by
  have recordCalled :(.ok (.Ok completed),recorded)∈support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire)
          (RegistrationBeaconRecordExecutor.begin capability))).run agreed) :=by
    simpa only [RegistrationBeaconRecordExecutor.begin,started,RegistrationBeaconRecordExecutor.continueWith] using recordRun
  have acceptedCoherent : (RegistrationResponseExecutor.acceptedResponse original packet adDigest).control.expected_server_binding =
      (RegistrationResponseExecutor.acceptedResponse original packet adDigest).binding.server_pin.binding := by
    simpa only [RegistrationResponseExecutor.acceptedResponse, RegistrationResponseExecutor.completedBinding_pin] using coherent
  have compared := RegistrationNativeLoggedStagedRootAgreement.root_or_marker setup checks functional representation created work result sampled
    initPacket initAuth serverBefore serverAfter accepted receipt owner oneTime token tokenEq matched
    (RegistrationResponseExecutor.acceptedResponse original packet adDigest) acceptedCoherent capability middle agreed agreementRun target row publicKey prekey serverIdentity ephemeral kemCiphertext
  obtain ⟨_input, _atRoot, _original, _collected, _fields, _prepared, literal, _stateEq⟩ :=
    RegistrationNativeBeaconAgreementInputReceipt.local_cut setup checks representation created owner oneTime (RegistrationResponseExecutor.acceptedResponse original packet adDigest) acceptedCoherent capability middle agreed agreementRun
  have sameBinding : capability.binding = RegistrationResponseExecutor.completedBinding original adDigest := congrArg agreement.BeaconAgreement.binding literal
  have sameCiphertext : capability.application_ciphertext = packet.application := congrArg agreement.BeaconAgreement.application_ciphertext literal
  obtain ⟨serverBefore, serverAfter, serverRun, serverExtension⟩ := issued
  obtain ⟨ad, sender, assigned, plaintext, completedBinding⟩ := RegistrationNativePlatformPairedRecord.run coins setup checks wire representation created
    view correct failure allocation erased rawAllocation serializer serverInitial hashed serverBefore serverAfter capability completed agreed recorded cache
    serverRun serverExtension recordCalled extension (ciphertext.trans sameCiphertext.symm) collisionFree
  have contents : RegistrationNativeCompletionContents.Outcome serverInitial (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability completed application :=
    ⟨sameBinding, sameCiphertext, ad.trans (congrArg session.CompletedRegistrationBinding.associated_data sameBinding), sender,
      assigned, returned.trans plaintext, by simpa only [sameBinding, RegistrationResponseExecutor.acceptedResponse] using completedBinding⟩
  obtain ⟨_serverDigest, _serverBinding, _completed, _same, serverApplicationEq, _started⟩ :=
    (RegistrationNativeServerBindingReceipt.initial_root control stagePin availability token.agreement serverApplication serverInitial serverStarted).2
  refine ⟨contents, ?_, ?_⟩
  · exact contents.2.2.2.2.2.1.trans (congrArg TranscriptAuthParts.absSlice serverApplicationEq)
  · rcases compared with rootEq | failed
    · exact Or.inl ⟨rootEq, RegistrationNativeInitializerAgreement.kernels crypto setup.source control stagePin availability token.agreement capability
        serverApplication serverInitial beaconInitial serverStarted started rootEq⟩
    · exact Or.inr failed

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementGivenCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementGivenCut.given_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementGivenCut.given_cut
