import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPin
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath
import BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetDesignatedRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerInputs
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
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
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
variable (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem
  (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller
local notation "State" => RegistrationNativePlatformLorSourceAlignment.State source Platform Private
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State
include contract

/-- Original broad owner designation supplies the same actual successful source finish, challenge ciphertext and configured owner pin. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2).2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2).1.keys=[])
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Fin budget.accept) (owner : Nat)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.owner owner)=some (session,target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val) :
    owner=target.2.val ∧ ∃ raw packet application pre post, ∃ first last : FullState,
      observed.2.1.transcript=pre++⟨.inl (.inr (.finish target.2.val raw)),some application⟩::post ∧
      Path full (RegistrationNativeLedger.empty,before) pre first ∧
      (.ok (some application),last.2) ∈ support ((typed (.inr (.finish target.2.val (some packet)))).run first.2) ∧
      Path full last post observed.2 ∧ RegistrationNativeWire.readResponse wire raw=some packet ∧
      packet.public.kem_cipher_text=PqxdhAcceptedRegistration.ciphertextArray challenge ∧
      ∀ current, first.2.1.1.beacons[target.2.val]?=some current →
        current.view.pin.binding.identity_public_key=before.1.1.server.pin.binding.identity_public_key := by
  obtain ⟨call,_marker,first,last,firstEq,lastEq,prior,called,later,retained⟩ :=
    RegistrationNativePlatformLorSourceDesignatedRetained.designated_retained setup checks source sign target.2.val target.1.val publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
      target.2.val pairs chosen.1 challenge implementation kem nativeInput contract
      serverKeyId bounds mode work budget bounded reserved before initialCounter initialMarker ownersEmpty keysEmpty observed supported
      session target.2 chosen.2 chosenAt (.owner owner) designated accepted
  obtain ⟨ready,authenticated,collected,stored,reference,agreement,verified,ciphertext,atom,readyAtom,acceptedKeys⟩ := retained
  have storedLast : last.2.1.1.server.sessions[session.val]?=some (some ready) := by
    rw [←lastEq]
    exact stored
  have ledger := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  have readyCiphertext : ready.agreement.pending.kem_ciphertext=PqxdhAcceptedRegistration.ciphertextArray challenge := by
    rw [agreement]
    exact ciphertext
  have encoded : ∀ response, PqxdhDeploymentTranscript.buildOf observed.2.1.ledger.transcript session.val=some response →
      RegistrationNativeResponseCiphertext.EncodedFrom (RegistrationNativeWire.Wire.encodeResponse wire) (PqxdhAcceptedRegistration.ciphertextArray challenge) response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom (RegistrationNativeWire.Wire.encodeResponse wire) before.1.1.server.pin.binding.identity_public_key response.serialized := by
    intro response built
    rw [ledger] at built
    obtain ⟨payload,member⟩ := RegistrationNativePlatformSecretWordBuildChronology.original_build observed.2.1.transcript session.val response built
    rw [call.recorded] at member
    obtain ⟨buildFirst,buildLast,_left,_right,_recorded,beforeBuild,built,_afterBuild,selectedReady⟩ :=
      RegistrationNativePlatformLorSourceBuildChronology.response setup checks wire source sign target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper reservePackets implementation serverKeyId bounds call.raw call.packet session.val call.decoded prior called later ready storedLast payload response member
    obtain ⟨actual,actualStored,actualCiphertext,actualIdentity⟩ :=
      RegistrationNativePlatformLorSourceResponseFields.full setup checks wire source sign
        target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation
        serverKeyId bounds session.val payload response buildFirst buildLast built
    have sameReady : actual=ready := Option.some.inj (Option.some.inj (actualStored.symm.trans selectedReady))
    subst actual
    have firstPin := RegistrationNativePlatformLorSourcePolicies.path_pin setup checks wire sign target.2.val target.1.val publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds prior
    have acceptedPin := RegistrationNativePlatformLorSourcePolicies.path_pin setup checks wire sign target.2.val target.1.val publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds
      (RegistrationNativeSecretWordTargetPath.Path.cons (.inl (.inr (.accept call.raw))) (some session.val) first last last [] called (.nil last))
    have buildPin := RegistrationNativePlatformLorSourcePolicies.path_pin setup checks wire sign target.2.val target.1.val publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds beforeBuild
    have samePin : buildFirst.2.1.1.server.pin=before.1.1.server.pin := buildPin.trans (acceptedPin.trans firstPin)
    rw [readyCiphertext] at actualCiphertext
    rw [samePin] at actualIdentity
    exact ⟨actualCiphertext,actualIdentity⟩
  obtain ⟨sameOwner,raw,summaryPin,finished,packet,decoded,packetCiphertext⟩ :=
    RegistrationNativeOwnerLinkedFields.owner setup.source.crypto wire RegistrationNativePlatformConcreteSource.response_readback
      serverKeyId budget observed.2.1.ledger.transcript owner session target.2 designated
      (PqxdhAcceptedRegistration.ciphertextArray challenge) before.1.1.server.pin.binding.identity_public_key encoded
  subst owner
  have actualPath := RegistrationNativePlatformLorSourceAcceptedCall.full_path setup checks wire source sign target.2.val target.1.val publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds mode work before observed supported
  rw [ledger] at finished
  obtain ⟨application,member⟩ := RegistrationNativeSecretWordTargetOwnerCallPath.original_finish observed.2.1.transcript target.2.val raw finished
  obtain ⟨pre,post,recorded⟩ := List.mem_iff_append.mp member
  obtain ⟨first,last,beforeFinish,finishedCall,afterFinish⟩ := RegistrationNativeSecretWordTargetPath.split full actualPath pre _ post recorded
  have rawCall := finishedCall
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at rawCall
  obtain ⟨⟨reply,reached⟩,rawReached,returned⟩ := rawCall
  have replyEq : reply=some application := congrArg Prod.fst returned
  have stateEq : reached=last.2 := congrArg (fun result => result.2.2) returned
  subst reply
  rw [stateEq,RegistrationNativeRawAdapter.finish_state,support_map] at rawReached
  obtain ⟨⟨typedReply,current⟩,typedReached,returned⟩ := rawReached
  change (RegistrationNativeRawAdapter.resultOption typedReply,current)=(some application,last.2) at returned
  cases actual : typedReply with
  | fail error | div => simp [actual,RegistrationNativeRawAdapter.resultOption] at returned
  | ok answer =>
    simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at returned
    obtain ⟨optionalEq,currentEq⟩ := returned
    subst answer
    rw [currentEq,decoded] at typedReached
    refine ⟨rfl,raw,packet,application,pre,post,first,last,recorded,beforeFinish,?_,afterFinish,decoded,packetCiphertext,?_⟩
    · simpa only [actual] using typedReached
    · intro current found
      rw [ledger,recorded] at summaryPin
      have currentPin := RegistrationNativePlatformLorSourceOwnerPin.owner setup checks wire source sign target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased
        helper writer implementation serverKeyId bounds before ownersEmpty pre (⟨.inl (.inr (.finish target.2.val raw)),some application⟩::post)
        first beforeFinish target.2.val current found before.1.1.server.pin.binding.identity_public_key serverKeyId summaryPin
      exact congrArg (fun binding => binding.identity_public_key) currentPin
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerInputs

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerInputs.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerInputs.selected
