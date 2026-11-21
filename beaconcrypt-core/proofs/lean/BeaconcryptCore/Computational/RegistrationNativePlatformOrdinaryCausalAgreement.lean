-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalRecordStage
import BeaconcryptCore.Computational.RegistrationNativePlatformLoggedSourceStageAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemMatchedToken
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemRows
import BeaconcryptCore.Computational.RegistrationNativePlatformActualTupleReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformCausalAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformActualMatchedTuple
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemTokenRoot
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemActualBlocks

/-! The selected single runtime derives an actual earlier same-run staged partner for every protected successful finish outside its common origin/cache/recipient exceptions. The token, collector, family row, root, both initializers and source application/AD contents all belong to that execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {Platform E : Type}
variable {ι KemSK Value AD PT CT : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
variable (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
local notation "helper" => AdapterRecordRawBytes.helper rawAllocation serializer
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)

open RegistrationNativeStageTrace (Call)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativePlatformInitializedAgreement (opened)
open PqxdhRefinement
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
local notation "coins" => RegistrationNativePlatformMldsaProgram.coins

/-- All reached source contents and the root-or-actual-recipient-failure alternative at one successful corrected finish. -/
def Outcome (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : RegistrationNativeBeaconFrontend.Owner source) (original : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes) (before : Local n KemSK source)
    (token : peer.ConsumedRegistration)
    (serverInitial : registration.ServerInitialKdf) (serverApplication : Slice U8) : Prop :=
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
      token.agreement.root.bytes = capability.root.bytes ∧
      RegistrationNativeInitializedInitializers.Initializers crypto setup.source token.agreement capability serverInitial beaconInitial

omit primitives in
private theorem source_lower {V : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State V) (before : Native) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run (opened before) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run, opened,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- Actual prior issuance and this execution's nonfiring recipient marker give one earlier source partner with full reached contents and both equal-root initializer streams. -/
theorem path (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (correct : view.Correct)
    (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional))
    (history : History n source Value Platform) (returned : result.2.1.1.1.1 = some history)
    (execution : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history result.2.1.1.1.2 result.2.1.2)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Whole) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ execution.calls)
    (found : beforeFinish.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish.1))))
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache execution.finalNative))
    (marker : result.2.2 ≠ true) :
    ∃ leading trailing serverCall,
      execution.calls=leading++(⟨.inr (.finish index (some packet)),beforeFinish,.ok (some application),afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole)::trailing ∧
      serverCall∈leading ∧ ∃ receipt serverIndex serverInput,
      ∃ stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) view failure allocation erased helper
        serverIndex serverInput serverCall.before.1.server serverCall.after.1.server receipt,
      serverCall.query = .inr (.build serverIndex serverInput) ∧
      Outcome source crypto setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) representation execution.initial.created owner pending oneTime index packet application
        (opened beforeFinish.1) stage.token stage.initial stage.plaintext := by
  obtain ⟨leading, trailing, serverCall, receipt, serverIndex, serverInput, stage, split, prefixRun, suffixRun,
      earlier, queryEq, _payload, identity, ephemeral, kem, ciphertext, _assigned, initHash⟩ :=
    RegistrationNativePlatformOrdinaryCausalRecordStage.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId execution.initial execution.startup
        previous execution.calls (execution.finalNative, result.2.1.1.1.2) execution.reached index pending packet beforeFinish afterFinish application member issued
  let finishCall : Call RegistrationNativeRawAdapter.TypedSpec Whole := ⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩
  obtain ⟨_leading, _trailing, _split, _prefix, finished, _suffix⟩ := execution.reached.member finishCall member
  have afterExtension := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer suffixRun).1
  have beforeExtension := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (.cons finishCall finished _ _ suffixRun)).1
  have serverMember : serverCall ∈ execution.calls := by rw [split]; exact List.mem_append_left _ earlier
  obtain ⟨adDigest, completedBinding, completedAt, initialBinding, _application, _root⟩ :=
    (RegistrationNativeServerBindingReceipt.initial_root stage.current.control stage.pin stage.availability stage.token.agreement stage.plaintext stage.initial stage.admitted).2
  obtain ⟨expectedBinding, expectedAt, _pin, hashRetained, _identity, _digest, _consistent⟩ :=
    BeaconcryptCore.Refinement.SessionBinding.complete_refines stage.token.agreement.binding adDigest
  have completedSame : expectedBinding = completedBinding := RustM.ok.inj (expectedAt.symm.trans completedAt)
  have retained := (RegistrationNativeServerContents.path_contents stage.initial stage.hashed stage.path).1
  have tokenHash : stage.token.agreement.binding.init_hash = pending.binding.init_hash :=
    (hashRetained ▸ congrArg (fun binding : session.CompletedRegistrationBinding => binding.init_hash)
      ((retained.trans initialBinding).trans completedSame.symm)).symm.trans initHash
  obtain ⟨initPacket, handle, first, last, accepted, cut, tokenEq, tuple⟩ := RegistrationNativePlatformOrdinaryKemMatchedToken.taken setup checks wire route representation source
    ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional result supported history returned execution
      serverCall serverMember serverIndex stage.token stage.current stage.taken finishCall member index owner pending oneTime found phase tokenHash collisionFree
  obtain ⟨_acceptLeading, _acceptTrailing, _acceptSplit, beforeAccept, -, afterAccept⟩ := execution.reached.member
    (⟨.inr (.accept initPacket), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) accepted
  have extension := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer afterAccept).1
  obtain ⟨matched⟩ := RegistrationNativePlatformActualTupleReceipt.receipt setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation execution.initial.created initPacket
    { RegistrationNativeKemServerState.ofNative first.1 with parsedAccepts := first.1.parsedAccepts + 1 }
    (RegistrationNativeKemServerState.ofNative last.1) first.2 last.2 handle result.2.1.1.2 cut stage.token tokenEq owner oneTime
      (RegistrationNativeWorldCache.cache execution.finalNative) extension tuple
  have firstPin := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer beforeAccept).2
  have configuredPin := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer prefixRun).2
  have matchedFinal : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation execution.initial.created owner oneTime stage.token
      beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache execution.finalNative) :=
    { matched with pinEq := matched.pinEq.trans (firstPin.trans configuredPin.symm) }
  have facts := RegistrationNativePlatformOrdinaryAgreementFacts.initialized setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId execution.initial execution.startup previous beforeFinish leading prefixRun
  have prekey := facts.2.1 owner (List.mem_of_getElem? found)
  have coherent := RegistrationNativeBeaconCoherence.pending beforeFinish.1.beacons facts.2.2 index owner found pending oneTime phase
  have startupPin := RegistrationNativeServerPinStartup.start_pin setup source ensureInit identityIndex serverKeyId execution.initial execution.startup
  have configuredIdentity : beforeFinish.1.server.pin.binding.identity_public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys execution.initial.created.seed).ed25519 := by
    rw [configuredPin, startupPin.1]
    exact (RegistrationNativeStartupIdentity.identity setup source ensureInit identityIndex serverKeyId execution.initial execution.startup).2
  obtain ⟨_binding, candidateEq, _rest⟩ := RegistrationNativeServerContents.path_contents stage.initial stage.hashed stage.path
  have stageIdentity := RegistrationNativeMatchedServerPin.initial_identity setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation execution.initial.created owner oneTime stage.token
    beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache execution.finalNative) matchedFinal stage.current.control stage.pin stage.availability stage.plaintext stage.initial stage.admitted
  have packetIdentity : packet.public.identity_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys execution.initial.created.seed).ed25519 :=
    identity.symm.trans ((congrArg (fun value => value.server_identity_public_key) candidateEq).trans (stageIdentity.trans configuredIdentity))
  obtain ⟨_serverIdentity, _beaconIdentity, stageEphemeral, stageKem⟩ := RegistrationNativeServerPublicContents.initial
    stage.current.control stage.pin stage.availability stage.token.agreement stage.plaintext stage.initial stage.admitted
  have packetEphemeral : packet.public.ephemeral_key = stage.token.agreement.pending.ephemeral_public_key :=
    ephemeral.symm.trans ((congrArg (fun value => value.ephemeral_public_key) candidateEq).trans stageEphemeral)
  have packetKem : packet.public.kem_cipher_text = stage.token.agreement.pending.kem_ciphertext :=
    kem.symm.trans ((congrArg (fun value => value.kem_ciphertext) candidateEq).trans stageKem)
  obtain ⟨_buildLeading, _buildTrailing, _buildSplit, _beforeBuild, _built, afterBuild⟩ := prefixRun.member serverCall earlier
  have recordExtension := stage.cacheExtension.trans ((RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer afterBuild).1.trans beforeExtension)
  have recordCut : RegistrationNativePlatformSourceFinishContents.RecordCut (n := n) coins setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) view failure allocation erased rawAllocation serializer
      stage.initial stage.hashed (RegistrationNativeWorldCache.cache execution.finalNative) :=
    ⟨(stage.recordBefore, stage.recordPlatform), (stage.recordAfter, stage.afterRecordPlatform),
      (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mpr stage.recordCalled, recordExtension⟩
  obtain ⟨target, row, publicKey⟩ := RegistrationNativePlatformOrdinaryKemRows.selected setup checks wire route representation source
    ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded functional result supported history execution
      finishCall member index owner found
  have finishSupported : ((.ok (some application), afterFinish.1), afterFinish.2) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation execution.initial.created source execution.initial.credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.finish index (some packet)))).run beforeFinish.1).run beforeFinish.2) := by
    simp only [RegistrationNativeStageTrace.Executed, RegistrationNativePlatformOrdinaryKemClientJournal.actual,
      RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at finished
    obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := finished
    change (value, (native, platform)) = (.ok (some application), afterFinish) at same
    have valueEq : value = .ok (some application) := congrArg Prod.fst same
    have nativeEq : native = afterFinish.1 := congrArg (fun result => result.2.1) same
    have platformEq : platform = afterFinish.2 := congrArg (fun result => result.2.2) same
    simp only [StateT.run]
    simpa only [valueEq, nativeEq, platformEq, finishCall] using called
  rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at finishSupported
  have actual : (.ok (some application), afterFinish.1) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation execution.initial.created
        (RegistrationNativePlatformBeaconFinish.finish setup source (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index (some packet))).run beforeFinish.1) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ beforeFinish.2 afterFinish.2 finishSupported
  rw [source_lower, support_map] at actual
  obtain ⟨⟨reply, localAfter⟩, called, same⟩ := actual
  have replyEq : reply = .ok (some application) := congrArg Prod.fst same
  cases replyEq
  have cacheEq : RegistrationNativeWorldCache.cache localAfter.2.2 = RegistrationNativeWorldCache.cache afterFinish.1 :=
    congrArg (fun result => RegistrationNativeWorldCache.cache result.2) same
  obtain ⟨adDigest, aborted, middle, agreed, recorded, capability, completed, beaconInitial, moved, authenticated, agreementRun, recordRun,
    started, sameInitial, contents, applicationEq, compared⟩ :=
      RegistrationNativePlatformLoggedSourceStageAgreement.finish crypto coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) representation execution.initial.created view correct failure allocation erased rawAllocation serializer
        owner pending oneTime index packet application (opened beforeFinish.1) localAfter found phase called coherent prekey
        ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous)
        result functional supported initPacket cut.receipt.authenticated cut.receipt.root.beforeAgreement cut.receipt.root.afterAgreement cut.receipt.root.accepted cut.receipt.root.root
          stage.token tokenEq tuple target row publicKey (RegistrationNativeWorldCache.cache execution.finalNative) packetIdentity packetEphemeral packetKem
            stage.current.control stage.pin stage.availability stage.plaintext stage.initial stage.hashed stage.admitted recordCut
              (cacheEq ▸ afterExtension) ciphertext collisionFree
  have paired := compared.resolve_right marker
  exact ⟨leading,trailing,serverCall,split,earlier,receipt,serverIndex,serverInput,stage,queryEq,adDigest,aborted, middle, agreed, recorded, capability, completed, beaconInitial,
    moved, authenticated, agreementRun, recordRun, started, sameInitial, contents, applicationEq, paired⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalAgreement.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalAgreement.path
