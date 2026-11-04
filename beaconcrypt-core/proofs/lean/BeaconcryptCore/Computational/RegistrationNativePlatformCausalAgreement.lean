-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCausalRecordStage
import BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput
import BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts
import BeaconcryptCore.Computational.RegistrationNativeMatchedServerPin
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceStageAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformInitializedAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame

/-! An actual corrected source finish with a prior unsigned Server issuance has one earlier same-run staged partner with complete contents. The earlier record, token, actual generated tuple, root operands, both initializer streams and application are derived from the actual initialized path. Root agreement has the explicit alternative of a genuine primitive recipient-failure sample; no perfect KEM correctness or completed Server peer is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCausalAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformInitializedAgreement (opened)
variable {n : Nat} {E Platform ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

/-- All reached source contents and the root-or-actual-recipient-failure alternative at one successful corrected finish. -/
def Outcome (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (original : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes) (before : Local n KemSK source)
    (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverReceipt : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token pin cache)
    (serverInitial : registration.ServerInitialKdf) (serverApplication : Slice U8) : Prop :=
    ∃ aborted middle agreed recorded capability completed beaconInitial,
      original.aborted_state = .ok aborted ∧
      (.ok (.Ok (⟨original, packet⟩ : registration.AuthenticatedResponse)), middle) ∈ support
        ((lower setup checks representation created (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin original (.Some packet)))).run
            (RegistrationNativePlatformCompletionReceipt.consumed before index aborted)) ∧
      (.ok (.BeaconComplete capability), agreed) ∈ support ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon ⟨original, packet⟩))).run middle) ∧
      (.ok (.Ok completed), recorded) ∈ support ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run agreed) ∧
      registration.begin_beacon_completion capability = .ok beaconInitial ∧ beaconInitial.agreement = capability ∧
      RegistrationNativeCompletionContents.Outcome serverInitial ⟨original, packet⟩ capability completed application ∧
      application = TranscriptAuthParts.absSlice serverApplication ∧
      ((token.agreement.root.bytes = capability.root.bytes ∧
        RegistrationNativeInitializedInitializers.Initializers crypto setup.source token.agreement capability serverInitial beaconInitial) ∨
        ∃ (beaconInput : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) (atRoot : Local n KemSK source),
          (some beaconInput, atRoot) ∈ support ((lower setup checks representation created
            (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
              (simulateQ (RegistrationBeaconAgreementRoot.callbacks ⟨original, packet⟩)
                (PqxdhBeaconPhase2Preparation.collect () false true () [])))).run middle) ∧
          RegistrationNativeRecipientFailure.FailureAt setup middle.2.2.pool owner.kemHandle serverReceipt.root.collected beaconInput)

variable [primitive : AdapterSealPrimitive.Operations]
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree

omit primitive in
private theorem source_lower {Value : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) (before : Native) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run (opened before) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run, opened,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- Prior unsigned Server issuance supplies the exact earlier source partner and all staged contents on the same initialized corrected path. -/
theorem path (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (previous : Platform) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole)
    (reached : Path (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer) (initial.state, previous) calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Whole) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls)
    (found : beforeFinish.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish.1))))
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final.1)) :
    ∃ serverCall ∈ calls, ∃ receipt serverIndex serverInput,
      ∃ stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup wire view failure allocation erased (AdapterRecordRawBytes.helper rawAllocation serializer)
        serverIndex serverInput serverCall.before.1.server serverCall.after.1.server receipt,
      serverCall.query = .inr (.build serverIndex serverInput) ∧
      ∃ matched : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation initial.created owner oneTime stage.token
        beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1),
      Outcome crypto setup checks wire route representation initial.created owner pending oneTime index packet application (opened beforeFinish.1)
        stage.token beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1) matched stage.initial stage.plaintext := by
  obtain ⟨leading, trailing, serverCall, receipt, serverIndex, serverInput, stage, split, prefixRun, suffixRun,
      earlier, queryEq, _payload, identity, ephemeral, kem, ciphertext, _assigned, initHash⟩ :=
    RegistrationNativePlatformCausalRecordStage.path setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer ensureInit identityIndex serverKeyId initial startup
      previous calls final reached index pending packet beforeFinish afterFinish application member issued
  let finishCall : Call RegistrationNativeRawAdapter.TypedSpec Whole := ⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩
  obtain ⟨_leading, _trailing, _split, _prefix, finished, _suffix⟩ := reached.member finishCall member
  have afterExtension := RegistrationNativePlatformPathState.cache coins setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer suffixRun
  have beforeExtension := RegistrationNativePlatformPathState.cache coins setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer (.cons finishCall finished _ _ suffixRun)
  have earlierCollisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache beforeFinish.1) := by
    intro collision
    obtain ⟨one, two, left, right, distinct, firstAt, secondAt, equal⟩ := collision
    exact collisionFree ⟨one, two, left, right, distinct, beforeExtension firstAt, beforeExtension secondAt, equal⟩
  obtain ⟨matched⟩ := RegistrationNativePlatformMatchedServerInput.from_taken coins setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer ensureInit identityIndex serverKeyId initial startup
    previous beforeFinish leading prefixRun index owner pending oneTime found phase serverCall earlier serverIndex stage.token stage.current stage.taken
    stage.pin stage.plaintext stage.availability stage.initial stage.hashed stage.admitted stage.path initHash earlierCollisionFree
  let matchedFinal : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation initial.created owner oneTime stage.token
      beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1) :=
    { matched with cacheExtension := matched.cacheExtension.trans beforeExtension }
  have facts := RegistrationNativePlatformPathAgreementFacts.initialized coins setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer ensureInit identityIndex serverKeyId initial startup previous beforeFinish leading prefixRun
  have prekey := facts.2.1 owner (List.mem_of_getElem? found)
  have coherent := RegistrationNativeBeaconCoherence.pending beforeFinish.1.beacons facts.2.2 index owner found pending oneTime phase
  have configuredPin := RegistrationNativePlatformPathState.pin coins setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer prefixRun
  have startupPin := RegistrationNativeServerPinStartup.start_pin setup source ensureInit identityIndex serverKeyId initial startup
  have configuredIdentity : beforeFinish.1.server.pin.binding.identity_public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys initial.created.seed).ed25519 := by
    rw [configuredPin, startupPin.1]
    exact (RegistrationNativeStartupIdentity.identity setup source ensureInit identityIndex serverKeyId initial startup).2
  obtain ⟨_binding, candidateEq, _rest⟩ := RegistrationNativeServerContents.path_contents stage.initial stage.hashed stage.path
  have stageIdentity := RegistrationNativeMatchedServerPin.initial_identity setup checks wire route representation initial.created owner oneTime stage.token
    beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache beforeFinish.1) matched stage.current.control stage.pin stage.availability stage.plaintext stage.initial stage.admitted
  have packetIdentity : packet.public.identity_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys initial.created.seed).ed25519 :=
    identity.symm.trans ((congrArg (fun value => value.server_identity_public_key) candidateEq).trans (stageIdentity.trans configuredIdentity))
  obtain ⟨_serverIdentity, _beaconIdentity, stageEphemeral, stageKem⟩ := RegistrationNativeServerPublicContents.initial
    stage.current.control stage.pin stage.availability stage.token.agreement stage.plaintext stage.initial stage.admitted
  have packetEphemeral : packet.public.ephemeral_key = stage.token.agreement.pending.ephemeral_public_key :=
    ephemeral.symm.trans ((congrArg (fun value => value.ephemeral_public_key) candidateEq).trans stageEphemeral)
  have packetKem : packet.public.kem_cipher_text = stage.token.agreement.pending.kem_ciphertext :=
    kem.symm.trans ((congrArg (fun value => value.kem_ciphertext) candidateEq).trans stageKem)
  obtain ⟨_buildLeading, _buildTrailing, _buildSplit, _beforeBuild, _built, afterBuild⟩ := prefixRun.member serverCall earlier
  have recordExtension := stage.cacheExtension.trans ((RegistrationNativePlatformPathState.cache coins setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer afterBuild).trans beforeExtension)
  have recordCut : RegistrationNativePlatformSourceFinishContents.RecordCut (n := n) coins setup wire view failure allocation erased rawAllocation serializer
      stage.initial stage.hashed (RegistrationNativeWorldCache.cache final.1) :=
    ⟨(stage.recordBefore, stage.recordPlatform), (stage.recordAfter, stage.afterRecordPlatform),
      (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mpr stage.recordCalled, recordExtension⟩
  have finishSupported : ((.ok (some application), afterFinish.1), afterFinish.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation initial.created source initial.credential view failure allocation
        reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer (.inr (.finish index (some packet)))).run beforeFinish.1).run beforeFinish.2) := by
    simp only [RegistrationNativeStageTrace.Executed, RegistrationNativePlatformInitPendingJournal.callback,
      RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at finished
    obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := finished
    change (value, (native, platform)) = (.ok (some application), afterFinish) at same
    have valueEq : value = .ok (some application) := congrArg Prod.fst same
    have nativeEq : native = afterFinish.1 := congrArg (fun result => result.2.1) same
    have platformEq : platform = afterFinish.2 := congrArg (fun result => result.2.2) same
    simp only [StateT.run]
    simpa only [valueEq, nativeEq, platformEq, finishCall] using called
  have actual : (.ok (some application), afterFinish.1) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation initial.created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index (some packet))).run beforeFinish.1) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ beforeFinish.2 afterFinish.2 finishSupported
  rw [source_lower, support_map] at actual
  obtain ⟨⟨reply, localAfter⟩, called, same⟩ := actual
  have replyEq : reply = .ok (some application) := congrArg Prod.fst same
  cases replyEq
  have cacheEq : RegistrationNativeWorldCache.cache localAfter.2.2 = RegistrationNativeWorldCache.cache afterFinish.1 :=
    congrArg (fun result => RegistrationNativeWorldCache.cache result.2) same
  refine ⟨serverCall, ?_, receipt, serverIndex, serverInput, stage, queryEq, matchedFinal, ?_⟩
  · rw [split]
    exact List.mem_append_left _ earlier
  · exact RegistrationNativePlatformSourceStageAgreement.finish crypto coins setup checks wire route representation initial.created
      view correct failure allocation erased rawAllocation serializer owner pending oneTime index packet application (opened beforeFinish.1) localAfter
      found phase called coherent facts.1 prekey stage.token beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1)
      matchedFinal packetIdentity packetEphemeral packetKem stage.current.control stage.pin stage.availability stage.plaintext stage.initial stage.hashed
      stage.admitted recordCut (cacheEq ▸ afterExtension) ciphertext collisionFree

end BeaconcryptCore.Computational.RegistrationNativePlatformCausalAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCausalAgreement.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCausalAgreement.path
