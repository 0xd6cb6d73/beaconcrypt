-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementGivenCut
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

/-! A given moved source token and given successful first-record/Finish cuts retain their contents in the same initialized finite-recipient experiment. This uses actual operational cuts, rather than identifying compatible existential initializers after erasing the source observations. The callback chronology is retained separately by the source event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalGivenStage
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

theorem given_stage (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (correct : view.Correct)
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
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache execution.finalNative))
    (marker : result.2.2 ≠ true)

    (serverCall :Call RegistrationNativeRawAdapter.TypedSpec Whole) (serverMember :serverCall∈execution.calls)
    (serverIndex :Nat) (token :peer.ConsumedRegistration) (current :RegistrationServerFrontendCompiler.State n)
    (taken :RegistrationServerSdkSource.take serverIndex serverCall.before.1.server=(some token,current))
    (stagePin :session.ServerAuthenticationPin) (availability :pqxdh.KeyIdAvailability) (serverApplication :Slice U8)
    (serverInitial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
    (admitted :registration.begin_server_completion current.control stagePin availability token.agreement serverApplication=.ok (.Ok serverInitial))
    (recordPath :RegistrationServerRecordExecutor.Path serverInitial hashed)
    (identity :hashed.candidate.server_identity_public_key=packet.public.identity_key)
    (ephemeral :hashed.candidate.ephemeral_public_key=packet.public.ephemeral_key)
    (kem :hashed.candidate.kem_ciphertext=packet.public.kem_cipher_text)
    (initHash :hashed.binding.init_hash=pending.binding.init_hash)
    (ciphertext :hashed.ciphertext=packet.application)
    (issuedRecord :RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) view failure allocation erased rawAllocation serializer
      serverInitial hashed (RegistrationNativeWorldCache.cache execution.finalNative))
    (aborted :pqxdh.BeaconAborted)
    (middle agreed recorded :Local n KemSK source)
    (capability :agreement.BeaconAgreement) (completed :registration.CompletedBeacon) (beaconInitial :registration.BeaconInitialKdf)
    (authenticated :(.ok (.Ok (⟨pending,packet⟩ :registration.AuthenticatedResponse)),middle)∈support
      ((lower setup checks representation execution.initial.created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (.Some packet)))).run
        (RegistrationNativePlatformCompletionReceipt.consumed (opened beforeFinish.1) index aborted)))
    (agreementRun :(.ok (.BeaconComplete capability),agreed)∈support
      ((lower setup checks representation execution.initial.created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
          (RegistrationAgreementExecutor.beacon ⟨pending,packet⟩))).run middle))
    (recordRun :(.ok (.Ok completed),recorded)∈support
      ((lower setup checks representation execution.initial.created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
          (RegistrationBeaconRecordExecutor.fromInitial beaconInitial))).run agreed))
    (started :registration.begin_beacon_completion capability=.ok beaconInitial)
    (applicationEq :application=TranscriptAuthParts.absSlice completed.application)
    (recordExtension :RegistrationNativeWorldCache.cache recorded.2.2≤RegistrationNativeWorldCache.cache execution.finalNative) :
    RegistrationNativeCompletionContents.Outcome serverInitial ⟨pending,packet⟩ capability completed application ∧
      application=TranscriptAuthParts.absSlice serverApplication ∧
      token.agreement.root.bytes=capability.root.bytes ∧
      RegistrationNativeInitializedInitializers.Initializers crypto setup.source token.agreement capability serverInitial beaconInitial := by
  let finishCall : Call RegistrationNativeRawAdapter.TypedSpec Whole := ⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩
  obtain ⟨leading,_trailing,_split,prefixRun,_finished,_suffixRun⟩ := execution.reached.member finishCall member
  have initialBinding := (RegistrationNativeServerBindingReceipt.initial_root current.control stagePin availability token.agreement serverApplication serverInitial admitted).2.1
  have retained := (RegistrationNativeServerContents.path_contents serverInitial hashed recordPath).1
  have tokenHash : token.agreement.binding.init_hash = pending.binding.init_hash :=
    (congrArg (fun binding : session.RegistrationBinding => binding.init_hash) (retained.trans initialBinding)).symm.trans initHash
  obtain ⟨initPacket, handle, first, last, accepted, cut, tokenEq, tuple⟩ := RegistrationNativePlatformOrdinaryKemMatchedToken.taken setup checks wire route representation source
    ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional result supported history returned execution
      serverCall serverMember serverIndex token current taken finishCall member index owner pending oneTime found phase tokenHash collisionFree
  obtain ⟨_acceptLeading, _acceptTrailing, _acceptSplit, beforeAccept, _accepted, afterAccept⟩ := execution.reached.member
    (⟨.inr (.accept initPacket), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) accepted
  have pinned := RegistrationNativePlatformOrdinaryPathState.pinned setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer beforeAccept
      (RegistrationNativeServerPinCached.start setup ensureInit identityIndex serverKeyId execution.initial execution.startup)
  have extension := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer afterAccept).1
  obtain ⟨matched⟩ := RegistrationNativePlatformActualTupleReceipt.receipt setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation execution.initial.created initPacket
    { RegistrationNativeKemServerState.ofNative first.1 with parsedAccepts := first.1.parsedAccepts + 1 }
    (RegistrationNativeKemServerState.ofNative last.1) first.2 last.2 handle result.2.1.1.2 cut pinned token tokenEq owner oneTime
      (RegistrationNativeWorldCache.cache execution.finalNative) extension tuple
  have firstPin := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer beforeAccept).2
  have configuredPin := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation execution.initial.created execution.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer prefixRun).2
  have matchedFinal : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation execution.initial.created owner oneTime token
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
  obtain ⟨_binding, candidateEq, _rest⟩ := RegistrationNativeServerContents.path_contents serverInitial hashed recordPath
  have stageIdentity := RegistrationNativeMatchedServerPin.initial_identity setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation execution.initial.created owner oneTime token
    beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache execution.finalNative) matchedFinal current.control stagePin availability serverApplication serverInitial admitted
  have packetIdentity : packet.public.identity_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys execution.initial.created.seed).ed25519 :=
    identity.symm.trans ((congrArg (fun value => value.server_identity_public_key) candidateEq).trans (stageIdentity.trans configuredIdentity))
  obtain ⟨_serverIdentity, _beaconIdentity, stageEphemeral, stageKem⟩ := RegistrationNativeServerPublicContents.initial
    current.control stagePin availability token.agreement serverApplication serverInitial admitted
  have packetEphemeral : packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key :=
    ephemeral.symm.trans ((congrArg (fun value => value.ephemeral_public_key) candidateEq).trans stageEphemeral)
  have packetKem : packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext :=
    kem.symm.trans ((congrArg (fun value => value.kem_ciphertext) candidateEq).trans stageKem)
  obtain ⟨target, row, publicKey⟩ := RegistrationNativePlatformOrdinaryKemRows.selected setup checks wire route representation source
    ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded functional result supported history execution
      finishCall member index owner found
  have middleRow:=RegistrationNativeKemActualHandlePersistence.lower setup checks representation execution.initial.created
    (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) (RegistrationResponseExecutor.begin pending (.Some packet)))
    (RegistrationNativePlatformCompletionReceipt.consumed (opened beforeFinish.1) index aborted) middle _ authenticated owner.kemHandle (result.1 target).1 row
  have compared:=RegistrationNativePlatformPublicAdapterAgreementGivenCut.given_cut crypto coins setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) representation execution.initial.created view correct failure allocation erased rawAllocation serializer
    owner pending oneTime packet application middle agreed recorded capability completed beaconInitial agreementRun recordRun started applicationEq coherent prekey
    ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n:=n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous)
    result functional supported initPacket cut.receipt.authenticated cut.receipt.root.beforeAgreement cut.receipt.root.afterAgreement cut.receipt.root.accepted
    cut.receipt.root.root token tokenEq tuple target middleRow publicKey (RegistrationNativeWorldCache.cache execution.finalNative)
    packetIdentity packetEphemeral packetKem current.control stagePin availability serverApplication serverInitial hashed admitted issuedRecord recordExtension ciphertext collisionFree
  exact ⟨compared.1,compared.2.1,(compared.2.2.resolve_right marker).1,(compared.2.2.resolve_right marker).2⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalGivenStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalGivenStage.given_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalGivenStage.given_stage
