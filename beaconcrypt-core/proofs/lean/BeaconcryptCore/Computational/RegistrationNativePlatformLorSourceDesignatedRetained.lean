-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! Original broad designation and its literal accepted-call prefix retain the same selected source Ready under any persistent Word interpretation. Concrete publication/readback, original parsed chronology and the genuine marked collector are composed internally, with the complete platform/private suffix retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets


variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller

open RegistrationNativeSecretWordTargetCall (Call)
open RegistrationNativeSecretWordTargetPath (Path)
include contract in
/-- The original designated accept stores its own marked descriptor at the same session and exact source prefix. -/
theorem designated_retained (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : State source Platform Private) (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2).2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2).1.keys=[])
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Fin budget.accept) (ownerIndex : Fin budget.capacity) (privateKey : KemSK)
    (chosenAt : pairs[ownerIndex.val]?=some (publicKey,privateKey)) (handle : PqxdhDeploymentInterface.Handle)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget result.2.1.ledger.transcript handle=some (session,ownerIndex))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.2.1.transcript session.val selectedAccept) :
    ∃ call : Call (State source Platform Private) typed (fun current => current.1.1.parsedAccepts) wire selectedAccept result.2.1.transcript session.val,
      (kem call.first.2).2=none ∧
      ∃ first last : RegistrationNativeLedger.State × State source Platform Private,
        call.first=first.2 ∧ call.last=last.2 ∧
        Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
          (RegistrationNativeLedger.empty,before) call.pre first ∧
        (some session.val,last) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
          (.inl (.inr (.accept call.raw)))).run first) ∧
        Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) last call.post result.2 ∧
        RegistrationNativePlatformLorSourceAcceptFrontend.Retained setup.source.crypto call.packet challenge call.last.1.1.server session.val := by
  obtain ⟨call,marker,first,last,firstEq,lastEq,prior,called,suffix⟩ :=
    RegistrationNativePlatformLorSourceAcceptedCall.accepted_call setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation selected pairs publicKey challenge kem input contract
      serverKeyId bounds mode work before initialCounter initialMarker result supported session.val accepted
  obtain ⟨owner,raw,packet,keys,pair,ownerAt,acceptFound,parsed,keysFound,pairAt,_ownerHandle,ownerKey,keyAt⟩ :=
    RegistrationNativePlatformLorSourcePublication.designated_pair setup checks source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets selected pairs publicKey challenge implementation kem input contract
      serverKeyId bounds mode work budget bounded reserved before ownersEmpty keysEmpty result supported handle (session,ownerIndex) designated
  have pairEq : pair=(publicKey,privateKey) := Option.some.inj (pairAt.symm.trans chosenAt)
  have selectedKey : keys.2.pqKey=publicKey := keyAt.trans (congrArg Prod.fst pairEq)
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before result supported
  rw [consistent,call.canonical] at acceptFound
  have sameRaw : call.raw=raw := Option.some.inj acceptFound
  rw [←sameRaw,call.decoded] at parsed
  have samePacket : call.packet=packet := Option.some.inj parsed
  have matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet)).map
      (fun keys => keys.2.pqKey)=some publicKey := by
    rw [samePacket,keysFound,Option.map_some,selectedKey]
  have retained := RegistrationNativePlatformLorSourceAcceptFrontend.typed_retained setup checks implementation reserveRegistration
    selected pairs publicKey challenge kem input contract wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reservePeer reserveFrame erased helper writer call.packet call.first call.last session.val call.selected marker matching call.reached
  exact ⟨call,marker,first,last,firstEq,lastEq,prior,called,suffix,retained⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained.designated_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained.designated_retained
