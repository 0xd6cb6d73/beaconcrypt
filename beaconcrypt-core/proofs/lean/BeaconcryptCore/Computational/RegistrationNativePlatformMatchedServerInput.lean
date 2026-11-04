-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPathState
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace
import BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput

/-! Actual corrected initialized source pending/token journals supply the Server root-input receipt matching a reached Beacon tuple. Root equality, primitive recipient correctness and partner agreement are not premises. A same-stage response Init digest identifies the actual pending tuple outside the single common-cache collision event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeTokenSource (Present Born)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

variable [primitive : AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

/-- Actual source histories remove the caller-supplied matched Server root-input receipt from local staged agreement. -/
theorem from_taken (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (final : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl (initial.state, previous) calls final)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (found : final.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (buildCall : Call RegistrationNativeRawAdapter.TypedSpec Whole) (member : buildCall ∈ calls) (handle : Nat)
    (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (taken : RegistrationServerSdkSource.take handle buildCall.before.1.server = (some token, current))
    (pin : session.ServerAuthenticationPin) (plaintext : Slice U8) (availability : pqxdh.KeyIdAvailability)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (admitted : registration.begin_server_completion current.control pin availability token.agreement plaintext = .ok (.Ok serverInitial))
    (recordPath : RegistrationServerRecordExecutor.Path serverInitial hashed)
    (initHash : hashed.binding.init_hash = pending.binding.init_hash)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final.1)) :
    Nonempty (RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token
      final.1.server.pin (RegistrationNativeWorldCache.cache final.1)) := by
  obtain ⟨pendingCall, _member, origin, _leading, pendingTrailing, earlier, _split, _before, _called, afterPending, earlierFound, earlierPhase, metadata⟩ :=
    RegistrationNativePlatformInitPendingJournal.initialized_path coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer ensureInit identityIndex serverKeyId initial startup previous final calls reached
        index owner pending oneTime found phase
  obtain ⟨earlierInput⟩ := RegistrationNativePlatformInitPendingJournal.source_receipt coins setup checks representation created writer
    pendingCall index pending oneTime origin earlier earlierFound earlierPhase
  obtain ⟨pendingInput⟩ := RegistrationNativePlatformPendingTuple.transport setup earlier owner pending oneTime _ _ metadata
    (RegistrationNativePlatformPathState.cache coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer afterPending) earlierInput
  obtain ⟨buildLeading, buildTrailing, _buildSplit, beforeBuild, built, afterBuild⟩ := reached.member buildCall member
  have empty := RegistrationNativeTokenTrace.start_empty setup ensureInit identityIndex serverKeyId initial startup
  obtain ⟨acceptCall, acceptLeading, between, _acceptSplit, beforeAccept, accepted, betweenPath, tokenOrigin⟩ :=
    RegistrationNativePlatformTokenTrace.taken_origin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      beforeBuild empty handle token current taken
  obtain ⟨packet, recomputed, pinned, pinPlatform, events, authenticated, afterAuthentication, authPlatform, _queryEq, pinCalled, authCalled, birth, summaryEq⟩ := tokenOrigin
  have cachedPin := RegistrationNativePlatformPathState.pinned coins setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer beforeAccept
    (RegistrationNativeServerPinCached.start setup ensureInit identityIndex serverKeyId initial startup)
  obtain ⟨_recomputed, storedPin, checked⟩ := RegistrationNativePlatformTokenCacheSource.authentication coins setup (RegistrationNativeWire.ledgerCodec wire) route source.verify created packet
    acceptCall.before.1.server pinned afterAuthentication acceptCall.before.2 pinPlatform authPlatform recomputed events authenticated cachedPin pinCalled authCalled
  obtain ⟨afterAgreement, _history, agreed, _consumed, ⟨root⟩⟩ := RegistrationNativeTokenRootReceipt.born
    setup checks representation created packet authenticated afterAuthentication token birth
  have afterAccept : Path impl acceptCall.after (between ++ buildCall :: buildTrailing) final :=
    betweenPath.append (.cons buildCall built _ _ afterBuild)
  have extension := RegistrationNativePlatformPathState.cache coins setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer afterAccept
  have cacheEq : afterAuthentication.world.world.1.primitive.2 = RegistrationNativeWorldCache.cache acceptCall.after.1 :=
    congrArg (fun value : RegistrationSigningShared.State => value.2) summaryEq
  have authExtension : afterAuthentication.world.world.1.primitive.2 ≤ RegistrationNativeWorldCache.cache final.1 := by
    rw [cacheEq]
    exact extension
  have tokenBinding : token.agreement.binding = authenticated.binding := congrArg (fun value : agreement.ServerAgreement => value.binding) root.completedEq
  have initialBinding := (RegistrationNativeServerBindingReceipt.initial_root current.control pin availability token.agreement plaintext serverInitial admitted).2.1
  have retained := (RegistrationNativeServerContents.path_contents serverInitial hashed recordPath).1
  have authHash : authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray pendingInput.digest :=
    (congrArg (fun value : session.RegistrationBinding => value.init_hash) tokenBinding.symm).trans
      ((congrArg (fun value : session.RegistrationBinding => value.init_hash) (retained.trans initialBinding)).symm.trans
        (initHash.trans pendingInput.initHash))
  have startedSame : pendingInput.fingerprint.state.started = pendingInput.started := by
    simpa only [RegistrationNativeInitTupleSource.Fixed, RegistrationNativeInitTupleSource.metadata] using congrArg Prod.fst pendingInput.fixed
  have matched := RegistrationNativeInitTupleAgreement.registration setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
    created packet pinned afterAuthentication events authenticated checked (RegistrationNativeWorldCache.cache final.1)
      authExtension pendingInput.fingerprint.state pendingInput.started _ startedSame pendingInput.attached pendingInput.validated
        pendingInput.digest pendingInput.cached authHash collisionFree
  have fromAccept : Path impl acceptCall.before (acceptCall :: between ++ buildCall :: buildTrailing) final :=
    .cons acceptCall accepted _ _ afterAccept
  have pinEq := RegistrationNativePlatformPathState.pin coins setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer fromAccept
  exact ⟨⟨pinned, packet, events, authenticated, afterAuthentication, afterAgreement, checked, agreed, root, matched,
    storedPin.trans pinEq.symm, authExtension⟩⟩

/-- The actual complete initialized source journal derives the matched root-input receipt from its own pending and moved-token cuts. -/
theorem initialized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (Whole × List (Call RegistrationNativeRawAdapter.TypedSpec Whole)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler impl) work).run ((initial.state, previous), [])))
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (found : result.2.1.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (buildCall : Call RegistrationNativeRawAdapter.TypedSpec Whole) (member : buildCall ∈ result.2.2) (handle : Nat)
    (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (taken : RegistrationServerSdkSource.take handle buildCall.before.1.server = (some token, current))
    (pin : session.ServerAuthenticationPin) (plaintext : Slice U8) (availability : pqxdh.KeyIdAvailability)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (admitted : registration.begin_server_completion current.control pin availability token.agreement plaintext = .ok (.Ok serverInitial))
    (recordPath : RegistrationServerRecordExecutor.Path serverInitial hashed)
    (initHash : hashed.binding.init_hash = pending.binding.init_hash)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1.1)) :
    Nonempty (RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token
      result.2.1.1.server.pin (RegistrationNativeWorldCache.cache result.2.1.1)) := by
  exact from_taken coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
    ensureInit identityIndex serverKeyId initial startup previous result.2.1 result.2.2
    (RegistrationNativeStageTrace.path impl work (initial.state, previous) result supported) index owner pending oneTime found phase buildCall member handle
    token current taken pin plaintext availability serverInitial hashed admitted recordPath initHash collisionFree

end BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput.from_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput.from_taken

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput.initialized
