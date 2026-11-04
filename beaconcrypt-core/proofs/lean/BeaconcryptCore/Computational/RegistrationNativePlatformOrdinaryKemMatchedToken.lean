-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformActualMatchedTuple
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemTokenRoot
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemActualBlocks

/-! A moved token and reached pending owner in the selected single runtime determine the same actual Root collector and original Beacon public tuple. The source pin/authentication, earlier bundle and digest/cache chronology are derived from one complete initialized execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemMatchedToken
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {Platform E : Type}
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)

open RegistrationNativeStageTrace (Call)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
local notation "coins" => RegistrationNativePlatformMldsaProgram.coins

/-- Every moved source token matching a reached pending digest has its actual own logged Root collector on that original tuple. No desired root equality or perfect recipient correctness is supplied. -/
theorem taken (budget : Budget) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional))
    (history : History n source Value Platform) (returned : result.2.1.1.1.1 = some history)
    (path : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history result.2.1.1.1.2 result.2.1.2)
    (buildCall : Call RegistrationNativeRawAdapter.TypedSpec Whole) (member : buildCall ∈ path.calls)
    (index : Nat) (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (moved : RegistrationServerSdkSource.take index buildCall.before.1.server = (some token, current))
    (selectedCall : Call RegistrationNativeRawAdapter.TypedSpec Whole) (selected : selectedCall ∈ path.calls)
    (ownerIndex : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : selectedCall.before.1.beacons[ownerIndex]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (initHash : token.agreement.binding.init_hash = pending.binding.init_hash)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache path.finalNative)) :
    ∃ packet handle first last,
      (⟨.inr (.accept packet), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ path.calls ∧
      ∃ cut : RegistrationNativePlatformAcceptActualToken.SourceCut setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks route representation path.initial.created packet
        { RegistrationNativeKemServerState.ofNative first.1 with parsedAccepts := first.1.parsedAccepts + 1 }
        (RegistrationNativeKemServerState.ofNative last.1) first.2 last.2 handle result.2.1.1.2,
      token.agreement = cut.receipt.root.accepted ∧
      cut.receipt.authenticated.registration = {
        beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
        beacon_prekey_public_key := owner.prekeyPublic,
        beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
        beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic } := by
  obtain ⟨leading, trailing, _split, beforeSelected, selectedExecuted, following⟩ := path.reached.member selectedCall selected
  have beforeExtension := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation path.initial.created path.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (.cons selectedCall selectedExecuted _ _ following)).1
  obtain ⟨pendingCall, _pendingMember, origin, _pendingLeading, pendingTrailing, earlier, _pendingSplit, _beforePending, _pendingExecuted,
    afterPending, earlierFound, earlierPhase, metadata⟩ :=
      RegistrationNativePlatformOrdinaryInitPendingJournal.initialized_path setup checks wire route representation path.initial.created path.initial.credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId path.initial path.startup previous selectedCall.before leading beforeSelected
          ownerIndex owner pending oneTime found phase
  obtain ⟨earlierInput⟩ := RegistrationNativePlatformOrdinaryInitPendingJournal.source_receipt setup checks representation path.initial.created writer
    pendingCall ownerIndex pending oneTime origin earlier earlierFound earlierPhase
  have pendingExtension := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation path.initial.created path.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer afterPending).1
  obtain ⟨pendingInput⟩ := RegistrationNativePlatformPendingTuple.transport setup earlier owner pending oneTime _ _ metadata
    (pendingExtension.trans beforeExtension) earlierInput
  obtain ⟨packet, handle, first, last, accepted, cut, tokenEq⟩ := RegistrationNativePlatformOrdinaryKemTokenRoot.taken setup checks wire route representation source
    ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional result supported history returned path
      buildCall member index token current moved
  obtain ⟨_acceptLeading, _acceptTrailing, _acceptSplit, beforeAccept, _accepted, afterAccept⟩ := path.reached.member
    (⟨.inr (.accept packet), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) accepted
  have pinned := RegistrationNativePlatformOrdinaryPathState.pinned setup checks wire route representation path.initial.created path.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer beforeAccept
      (RegistrationNativeServerPinCached.start setup ensureInit identityIndex serverKeyId path.initial path.startup)
  have extension := (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation path.initial.created path.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer afterAccept).1
  have tuple := RegistrationNativePlatformActualMatchedTuple.tuple setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation path.initial.created packet
    { RegistrationNativeKemServerState.ofNative first.1 with parsedAccepts := first.1.parsedAccepts + 1 }
    (RegistrationNativeKemServerState.ofNative last.1) first.2 last.2 handle result.2.1.1.2 cut pinned token tokenEq owner pending oneTime
      (RegistrationNativeWorldCache.cache path.finalNative) pendingInput extension initHash collisionFree
  exact ⟨packet, handle, first, last, accepted, cut, tokenEq, tuple⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemMatchedToken

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemMatchedToken.taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemMatchedToken.taken
