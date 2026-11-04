import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotAt
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartners
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwnerExposure
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerExposure
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerSession
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposure
import BeaconcryptCore.Computational.RegistrationNativeSessionEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
/-! A successful current Server build appends exactly the stored Ready descriptor to its own installation trace under any persistent Word interpretation. The free source receipt retains the original reply, platform state, failed prefixes and full raw ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshot
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
open RegistrationNativeSecretWordInstallOrdinals (messages)
local notation "traceState" => RegistrationNativePlatformLorStatefulSupport.TracedState
  (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "traceTyped" => RegistrationNativePlatformLorStatefulSupport.traced implementation controller


variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped
local notation "FullState" => RegistrationNativeLedger.State × traceState
include contract

variable {ProviderState Physical : Type}

/-- The actual complete input and shared native/public ordinals turn opposite-role slot receipts into corrected session partners or the same final recovery exposure. -/
theorem from_snapshot (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : MlKemSharedSecret) (before : traceState)
    (initialTrace : before.2.1.events=[]) (initialSessions : before.1.1.server.sessions=[])
    (initialCounter : before.1.1.parsedAccepts=0) (ownersEmpty : before.1.1.beacons=[])
    (keysEmpty : (kem before.2.2).1.keys=[])
    {after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full (RegistrationNativeLedger.empty,before) entries after)
    (budget : PqxdhDeploymentInterface.Budget) (target : Fin budget.accept × Fin budget.capacity)
    (selectedOwnerEq : selected=target.2.val)
    (current : RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState Physical)
    (valid : RegistrationNativePlatformRecordPartnerSlotTrace.Valid
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate) current)
    (traceEq : current.2.1.events=after.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
    (publicHandles : ∀role,RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles role current.1.snapshot=
      RegistrationNativeInstallOrdinals.handles role after.1.transcript)
    (peerPosition ownerPosition : Nat) (peerReceipt ownerReceipt : RegistrationNativePlatformRecordSlotGhost.Receipt n)
    (peerFound : current.1.snapshot.installs[peerPosition]?=some peerReceipt)
    (ownerFound : current.1.snapshot.installs[ownerPosition]?=some ownerReceipt)
    (peerRole : peerReceipt.role=.server) (ownerRole : ownerReceipt.role=.beacon)
    (keyId : U64) (owner : Nat) (peerHandle : peerReceipt.handle=.peer keyId) (ownerHandle : ownerReceipt.handle=.owner owner)
    (slot : PqxdhRecordLiftInterface.Slot n) (peerSlot : peerReceipt.slot=some slot) (ownerSlot : ownerReceipt.slot=some slot)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) after.1.transcript target.1.val selectedAccept) :
    RegistrationNativeSessionEvents.CEPartners budget target (after.1.transcript.map RegistrationNativeInterface.Entry.erase) (.peer keyId) (.owner owner) ∨
      RegistrationNativeSecretWordAliasExposureBound.Exposure (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate after.2.2.1 := by
  have counts := RegistrationNativePlatformLorSourceInstall.path_counts setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation candidate serverKeyId bounds before initialTrace path
  have nativeCounts : ∀role,RegistrationNativeInstallOrdinals.Counts role current.2.1.events after.1.transcript := by
    intro role
    rw [traceEq]
    exact counts role
  obtain ⟨peerOrdinal,ownerOrdinal,peerMessage,ownerMessage,bytes,peerAt,ownerAt,peerFormed,ownerFormed,hidden⟩ :=
    RegistrationNativePlatformRecordPartnerSnapshotAt.same_slot setup seed scalar candidate current valid after.1.transcript publicHandles nativeCounts
      peerPosition ownerPosition peerReceipt ownerReceipt peerFound ownerFound peerRole ownerRole slot peerSlot ownerSlot
  rw [traceEq,peerHandle] at peerAt
  rw [traceEq,ownerHandle] at ownerAt
  exact RegistrationNativePlatformRecordPartners.partners_or_exposure setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation selected pairs publicKey challenge kem input contract
    serverKeyId bounds seed scalar candidate (setup.joint.staticDh seed (setup.dh.publicKey scalar)) before initialTrace initialSessions initialCounter ownersEmpty keysEmpty
    path budget target selectedOwnerEq peerOrdinal ownerOrdinal peerMessage ownerMessage keyId owner peerAt ownerAt bytes peerFormed ownerFormed hidden accepted

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshot.from_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshot.from_snapshot
