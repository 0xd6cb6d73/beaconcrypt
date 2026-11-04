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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerSession
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

/-- Any successful Server installation of the marked descriptor is the public peer built by the designated successful session. -/
theorem peer_of_session (candidate : MlKemSharedSecret) (before : traceState)
    (initialTrace : before.2.1.events=[]) (initialSessions : before.1.1.server.sessions=[])
    (initialCounter : before.1.1.parsedAccepts=0)
    {after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full (RegistrationNativeLedger.empty,before) entries after)
    (ordinal : Nat) (message : Message) (keyId : U64)
    (installed : RegistrationNativeSecretWordInstallOrdinals.At .server after.2.2.1.events after.1.transcript ordinal message (.peer keyId))
    (atom : message.kem=RegistrationNativeSecretWord.Word.atom) (session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) after.1.transcript session selectedAccept) :
    RegistrationNativeSessionEvents.peerOfSession (after.1.transcript.map RegistrationNativeInterface.Entry.erase) session=some keyId := by
  obtain ⟨pre,post,actualSession,payload,response,first,last,ready,recorded,key,earlier,called,later,stored,reference⟩ :=
    RegistrationNativePlatformRecordPartnerBuild.from_ordinal setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds candidate before initialTrace path ordinal message keyId installed
  have tracedContract := RegistrationNativePlatformLorSourceKemTrace.contract implementation kem input _ contract
  have readyAtom : ready.reference.kem=RegistrationNativeSecretWord.Word.atom := reference ▸ atom
  have sameSession := RegistrationNativePlatformRecordPartnerSessionSelected.atom_session setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (RegistrationNativePlatformLorStatefulSupport.trace implementation)
    selected pairs publicKey challenge (fun current => kem current.2) input tracedContract serverKeyId bounds earlier
    (.cons _ _ first last after post called later) initialSessions rfl initialCounter actualSession ready stored readyAtom session accepted
  have responseOf := RegistrationNativePlatformRecordPartnerBuildOnce.lookup setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds earlier actualSession payload response called post
  have records := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped)
      setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds) path
  simp only [RegistrationNativeLedger.empty,List.nil_append] at records
  unfold RegistrationNativeSessionEvents.peerOfSession
  rw [records,recorded,←sameSession,responseOf,Option.map_some,key]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerSession

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerSession.peer_of_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerSession.peer_of_session
