-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrekeyPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
import BeaconcryptCore.Computational.RegistrationNativeLinkedBuild
/-! Original broad peer designation and its transported public pin conjunct identify the exact protected Ready at the actual later successful moved-token build. The proof uses the current stateful source writer and retains one original run, all failed prefixes, complete platform/private state and its full suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedPeer
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity)
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "nativeInside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "publicPrekey" => setup.dh.publicKey scalar
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge))
local notation "traceImplementation" => RegistrationNativePlatformLorStatefulSupport.trace implementation
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed traceImplementation controller
local notation "State" => RegistrationNativePlatformLorStatefulSupport.TracedState
  (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State
include implementation kem seed scalar pairs chosen challenge contract
attribute [local irreducible] RegistrationNativeSecretWordKemEarly.early

/-- A broadly designated peer has the protected same Ready at its exact later successful source build. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2.2).2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2.2).1.keys=[])
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Fin budget.accept) (keyId : U64)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.peer keyId)=some (session,target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId observed.2.1.ledger.transcript (.peer keyId)) :
    ∃ payload response, ∃ ready : RegistrationNativeSecretWordMessage.ServerReady,
      ∃ (buildFirst buildLast : FullState) (left right : List RegistrationNativeInterface.Entry),
        response.keyId=keyId ∧ observed.2.1.transcript=left++⟨.inl (.inr (.build session.val payload)),some response⟩::right ∧
        Path full (RegistrationNativeLedger.empty,before) left buildFirst ∧
        (some response,buildLast) ∈ support ((full (.inl (.inr (.build session.val payload)))).run buildFirst) ∧
        Path full buildLast right observed.2 ∧
        buildFirst.2.1.1.server.sessions[session.val]?=some (some ready) ∧ ready.reference.kem=Word.atom ∧
        ∀ key, nativeInput ready.reference=some key → nativeInside key.head=true := by
  have traceContract := RegistrationNativePlatformLorSourceKemTrace.contract implementation kem nativeInput provider contract
  obtain ⟨call,_marker,traceFirst,traceLast,firstEq,lastEq,priorTrace,calledTrace,laterTrace,
      ready,_authenticated,collected,stored,reference,_agreement,_verified,_ciphertext,_atom,readyAtom,acceptedKeys⟩ :=
    RegistrationNativePlatformLorSourceDesignatedRetained.designated_retained setup checks source sign
      target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper reservePackets target.2.val pairs chosen.1 challenge traceImplementation (fun current => kem current.2) nativeInput traceContract
      serverKeyId bounds mode work budget bounded reserved before initialCounter initialMarker ownersEmpty keysEmpty observed supported
      session target.2 chosen.2 chosenAt (.peer keyId) designated accepted
  have ledger := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId budget observed.2.1.ledger.transcript (.peer keyId) (session,target.2) designated
  have acceptedOriginal := call.canonical
  rw [←ledger] at acceptedOriginal
  have prekey := RegistrationNativePlatformLorSourcePrekeyPublication.peer_prekey setup checks source sign
    target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets traceImplementation
    serverKeyId bounds mode work before observed ownersEmpty supported keyId session.val call.raw
    (RegistrationRootInput.candidate call.packet) (collected.plain.verified.identity,collected.plain.verified.keys) pinned plain acceptedOriginal
    (RegistrationNativeKemPublicTarget.candidate_read wire call.raw call.packet call.decoded) acceptedKeys
  obtain ⟨response,_raw,_accepted,_keys,linked,_rawFound,_acceptedFound,_keysFound,_ownerBound,_published⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId keyId
      observed.2.1.ledger.transcript session.val target.2.val plain
  rw [ledger] at linked
  obtain ⟨sameKey,payload,member⟩ := RegistrationNativeLinkedBuild.original observed.2.1.transcript keyId session.val response linked
  rw [call.recorded] at member
  have lastStored : traceLast.2.1.1.server.sessions[session.val]?=some (some ready) := by
    rw [←lastEq]
    exact stored
  obtain ⟨buildFirst,buildLast,left,right,recorded,beforeBuild,built,afterBuild,selectedReady⟩ :=
    RegistrationNativePlatformLorSourceBuildChronology.response setup checks wire source sign
      target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
      traceImplementation serverKeyId bounds call.raw call.packet session.val call.decoded priorTrace calledTrace laterTrace ready lastStored payload response member
  have throughAccept : Path full traceFirst [⟨.inl (.inr (.accept call.raw)),some session.val⟩] traceLast :=
    .cons _ _ _ _ _ [] calledTrace (.nil _)
  have buildPrefix := RegistrationNativeSecretWordTargetPathConcat.append full
    (RegistrationNativeSecretWordTargetPathConcat.append full priorTrace throughAccept) beforeBuild
  refine ⟨payload,response,ready,buildFirst,buildLast,
    (call.pre++[⟨.inl (.inr (.accept call.raw)),some session.val⟩])++left,right,sameKey,?_,buildPrefix,built,afterBuild,selectedReady,readyAtom,?_⟩
  · apply call.recorded.trans
    rw [recorded]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  · intro key realized
    rw [reference] at realized
    exact RegistrationNativeSecretWordTargetProtected.server_inside setup seed scalar RegistrationNativeSecretWordMessage.zero collected prekey key realized

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedPeer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedPeer.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedPeer.selected
