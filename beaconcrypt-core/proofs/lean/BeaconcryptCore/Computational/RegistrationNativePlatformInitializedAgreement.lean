-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInvariants
import BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun

/-! An actual successful corrected Platform finish after an actual initialized raw prefix has full staged contents and root-or-recipient-failure agreement. All current-owner generated KEM, prekey/scalar and pending coherence facts are derived from the initialized source execution. The earlier matched same-run token and actual source record cut remain explicit stage receipts; no root, initializer or protocol-security conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInitializedAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {E Platform Value ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]

def opened (before : RegistrationNativeExperiment.State n KemSK source) : Local n KemSK source :=
  (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))

omit primitive in
private theorem source_lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run (opened before) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run, opened,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- Current-owner hypotheses in local paired agreement are discharged by the actual initialized corrected raw prefix. -/
theorem initialized (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (progress : (Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source)
    (startPlatform currentPlatform : Platform)
    (progressed : (progress, currentPlatform) ∈ support
      ((RegistrationNativePlatformExperiment.run coins setup checks wire route representation initial.created source initial.credential
        view failure allocation reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer bounds mode work initial.state).run startPlatform))
    (owner : Owner source) (original : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes) (finished : RegistrationNativeExperiment.State n KemSK source) (nextPlatform : Platform)
    (found : progress.2.beacons[index]? = some owner) (phase : owner.phase = .initSent original oneTime)
    (supported : ((.ok (some application), finished), nextPlatform) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation initial.created source initial.credential
        view failure allocation reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer
        (.inr (.finish index (some packet)))).run progress.2).run currentPlatform))
    (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverReceipt : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation initial.created owner oneTime token pin cache)
    (serverIdentity : packet.public.identity_key = rootArray (setup.joint.publicKeys initial.created.seed).ed25519)
    (ephemeral : packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key)
    (kemCiphertext : packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext)
    (control : pqxdh.ServerState) (availability : pqxdh.KeyIdAvailability) (serverApplication : Slice U8)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (serverStarted : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability token.agreement serverApplication serverInitial)
    (issued : RegistrationNativePlatformSourceFinishContents.RecordCut (n := n) coins setup wire view failure allocation erased
      rawAllocation serializer serverInitial hashed cache)
    (extension : RegistrationNativeWorldCache.cache finished ≤ cache)
    (ciphertext : hashed.ciphertext = packet.application) (collisionFree : ¬ CacheHasCollision cache) :
    ∃ adDigest aborted middle agreed recorded capability completed beaconInitial,
      original.aborted_state = .ok aborted ∧
      (.ok (.Ok ((RegistrationResponseExecutor.acceptedResponse original packet adDigest) : registration.AuthenticatedResponse)), middle) ∈ support
        ((lower setup checks representation initial.created (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin original (.Some packet)))).run
            (RegistrationNativePlatformCompletionReceipt.consumed (opened progress.2) index aborted)) ∧
      (.ok (.BeaconComplete capability), agreed) ∈ support ((lower setup checks representation initial.created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon (RegistrationResponseExecutor.acceptedResponse original packet adDigest)))).run middle) ∧
      (.ok (.Ok completed), recorded) ∈ support ((lower setup checks representation initial.created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run agreed) ∧
      registration.begin_beacon_completion capability = .ok beaconInitial ∧ beaconInitial.agreement = capability ∧
      RegistrationNativeCompletionContents.Outcome serverInitial (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability completed application ∧
      application = TranscriptAuthParts.absSlice serverApplication ∧
      ((token.agreement.root.bytes = capability.root.bytes ∧
        RegistrationNativeInitializedInitializers.Initializers crypto setup.source token.agreement capability serverInitial beaconInitial) ∨
        ∃ (beaconInput : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) (atRoot : Local n KemSK source),
          (some beaconInput, atRoot) ∈ support ((lower setup checks representation initial.created
            (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
              (simulateQ (RegistrationBeaconAgreementRoot.callbacks (RegistrationResponseExecutor.acceptedResponse original packet adDigest))
                (PqxdhBeaconPhase2Preparation.collect () false true () [])))).run middle) ∧
          RegistrationNativeRecipientFailure.FailureAt setup middle.2.2.pool owner.kemHandle serverReceipt.root.collected beaconInput) := by
  have invariant := RegistrationNativePlatformOwnerInvariants.initialized coins setup checks wire route representation
    ensureInit identityIndex serverKeyId initial started view failure allocation reserveRegistration reservePeer erased
    (AdapterRecordRawBytes.helper rawAllocation serializer) writer bounds mode work progress startPlatform currentPlatform progressed
  have pending := RegistrationNativePlatformCoherenceRun.initialized coins setup checks wire route representation
    ensureInit identityIndex serverKeyId initial started view failure allocation reserveRegistration reservePeer erased
    (AdapterRecordRawBytes.helper rawAllocation serializer) writer bounds mode work progress startPlatform currentPlatform progressed
  have coherent : original.control.expected_server_binding = original.binding.server_pin.binding := by
    have valid := pending owner (List.mem_of_getElem? found)
    simpa only [phase, RegistrationNativeBeaconCoherence.PhaseCoherent] using valid
  have prekey := invariant.2 owner (List.mem_of_getElem? found)
  have actual : (.ok (some application), finished) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation initial.created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index (some packet))).run progress.2) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ currentPlatform nextPlatform supported
  rw [source_lower, support_map] at actual
  obtain ⟨⟨reply, localAfter⟩, called, same⟩ := actual
  have replyEq : reply = .ok (some application) := congrArg Prod.fst same
  cases replyEq
  have cacheEq : RegistrationNativeWorldCache.cache localAfter.2.2 = RegistrationNativeWorldCache.cache finished :=
    congrArg (fun result => RegistrationNativeWorldCache.cache result.2) same
  exact RegistrationNativePlatformSourceAgreement.finish crypto coins setup checks wire route representation initial.created
    view correct failure allocation erased rawAllocation serializer owner original oneTime index packet application (opened progress.2) localAfter
    found phase called coherent invariant.1 prekey token pin cache serverReceipt serverIdentity ephemeral kemCiphertext control availability serverApplication
    serverInitial hashed serverStarted issued (cacheEq ▸ extension) ciphertext collisionFree

end BeaconcryptCore.Computational.RegistrationNativePlatformInitializedAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitializedAgreement.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitializedAgreement.initialized
