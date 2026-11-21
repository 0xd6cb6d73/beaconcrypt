import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishOrdinal
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwnerExposure
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

omit primitive contract in
private theorem at_member (trace : RegistrationNativeSecretWordFrontendTrace.State) (ordinal : Nat) (message : Message)
    (found : (messages .beacon trace.events)[ordinal]?=some message) :
    RegistrationNativeSecretWordFrontendTrace.Event.install .beacon message ∈ trace.events := by
  have member := List.mem_of_getElem? found
  obtain ⟨event,present,encoded⟩ := List.mem_filterMap.mp member
  cases event with
  | install role actual =>
    simp only at encoded
    split at encoded
    · rename_i same
      subst role
      have equal : actual=message := Option.some.inj encoded
      exact equal ▸ present
    · cases encoded
  | _ => cases encoded

/-- The same native selected beacon installation belongs to the selected public owner or exposes the literal candidate in its own existing recovery trace. -/
theorem owner_or_exposure (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : MlKemSharedSecret) (target : Option PqxdhJointIdentity.DhOutput) (before : traceState)
    (initialTrace : before.2.1.events=[]) (ownersEmpty : before.1.1.beacons=[])
    (keysEmpty : (kem before.2.2).1.keys=[])
    {after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full (RegistrationNativeLedger.empty,before) entries after)
    (ordinal : Nat) (message : RegistrationNativeRelatedFamily.Message) (owner : Nat)
    (installed : RegistrationNativeInstallOrdinals.At .beacon
      (after.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) after.1.transcript ordinal message (.owner owner))
    (bytes : Pqxdh.Bytes)
    (formed : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message=some bytes)
    (hidden : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate bytes=true)
    : owner=selected ∨
      RegistrationNativeSecretWordAliasExposureBound.Exposure (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside target) candidate after.2.2.1 := by
  have evaluated := installed.1
  rw [RegistrationNativeSecretWordInstallOrdinals.messages_eval,List.getElem?_map] at evaluated
  obtain ⟨word,wordAt,wordEval⟩ := Option.map_eq_some_iff.mp evaluated
  have wordFormed : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar
      (RegistrationNativeSecretWordMessage.eval candidate word)=some bytes := wordEval ▸ formed
  have actual : RegistrationNativeSecretWordInstallOrdinals.At .beacon after.2.2.1.events after.1.transcript ordinal word (.owner owner) := ⟨wordAt,installed.2⟩
  rcases RegistrationNativePlatformRecordPartnerExposure.atom_or_exposure setup.joint setup.dh seed scalar candidate target
    after.2.2.1 .beacon word bytes (Or.inl (at_member after.2.2.1 ordinal word wordAt)) wordFormed hidden with atom | exposed
  · exact Or.inl (RegistrationNativePlatformRecordPartnerFinishOrdinal.owner_of_ordinal setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation selected pairs publicKey challenge kem input contract
      serverKeyId bounds candidate before initialTrace ownersEmpty keysEmpty path ordinal word owner actual atom)
  · exact Or.inr exposed
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwnerExposure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwnerExposure.owner_or_exposure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerOwnerExposure.owner_or_exposure
