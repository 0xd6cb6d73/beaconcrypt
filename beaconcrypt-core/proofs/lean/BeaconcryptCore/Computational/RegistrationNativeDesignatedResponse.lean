-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleCall
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetainedPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
import BeaconcryptCore.Computational.RegistrationNativeLinkedBuild
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPinSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerOrdinal
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand

/-! Every broadly designated peer handle with the retained public prekey equality has its protected native installation at the exact successful linked build. The proof takes no fresh-message claim or private guess. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDesignatedResponse
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetTracedSource (State project)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
  (outer : QueryImpl Combined ProbComp) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
  (selectedTarget : Fin budget.accept × Fin budget.capacity)
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "nativeInside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem (Fin.val (Prod.snd selectedTarget)) pairs (Prod.fst chosen) challenge
local notation "plainTyped" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign nativeInput nativeInside provider outer (Fin.val (Prod.snd selectedTarget)) (Fin.val (Prod.fst selectedTarget)) (setup.dh.publicKey scalar)
local notation "typed" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign nativeInput nativeInside provider outer (Fin.val (Prod.snd selectedTarget)) (Fin.val (Prod.fst selectedTarget)) (setup.dh.publicKey scalar)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State n KemSK source

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetTracedSource.typed RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordKemEarly.early

/-- Every successful response of the designated session retains its actual challenge ciphertext and current configured Server identity. -/
theorem encoded (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (before : State n KemSK source) (initialCounter : before.1.1.parsedAccepts = 0)
    (initialMarker : before.2.kem.2 = none) (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (actualPath : Path full (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (session : Fin budget.accept) (handle : PqxdhDeploymentInterface.Handle)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript handle = some (session, selectedTarget.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val selectedTarget.1.val) :
    ∀ response, PqxdhDeploymentTranscript.buildOf observed.2.1.ledger.transcript session.val = some response →
      RegistrationNativeResponseCiphertext.EncodedFrom wire.encodeResponse (PqxdhAcceptedRegistration.ciphertextArray challenge) response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom wire.encodeResponse before.1.1.server.pin.binding.identity_public_key response.serialized := by
  let plainObserved := (observed.1, (observed.2.1, project observed.2.2))
  have plainSupport := Set.mem_image_of_mem (Prod.map id (Prod.map id project)) supported
  rw [← support_map, RegistrationNativeSecretWordTargetTracedPath.erase_run setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode work before] at plainSupport
  obtain ⟨call, marker, traceFirst, traceLast, firstEq, lastEq, priorTrace, calledTrace, laterTrace⟩ :=
    RegistrationNativeDesignatedHandleCall.accepted_call setup checks wire route sign nativeInput nativeInside pairs chosen.1 challenge
      outer (setup.dh.publicKey scalar) serverKeyId bounds mode work budget selectedTarget before initialCounter initialMarker observed actualPath session accepted
  have prior := RegistrationNativeSecretWordTargetTracedPath.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds priorTrace
  have later := RegistrationNativeSecretWordTargetTracedPath.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds laterTrace
  have called := Set.mem_image_of_mem (Prod.map id (Prod.map id project)) calledTrace
  rw [← support_map, RegistrationNativeSecretWordTargetTracedPath.full setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds] at called
  simp only [Prod.map_def, id_eq] at prior later called
  rw [← firstEq] at prior called
  rw [← lastEq] at later called
  obtain ⟨publishedOwner, raw, packet, keys, found, accepted, parsed, publicAcceptedKeys, publicMatches⟩ :=
    RegistrationNativeSecretWordTargetPublic.designated_public setup checks wire route sign nativeInput nativeInside provider outer
      selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId readback bounds mode work (project before) plainObserved plainSupport budget
      handle (session, selectedTarget.2) designated
  obtain ⟨pair, pairAt, _handle, ownerKey⟩ := RegistrationNativeSecretWordTargetBornKey.full_born_key setup checks wire route sign nativeInput nativeInside
    selectedTarget.2.val pairs chosen.1 challenge outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode work budget
    bounded reserved (project before) ownersEmpty keysEmpty plainObserved plainSupport selectedTarget.2.val publishedOwner found
  have samePair : pair = chosen := Option.some.inj (pairAt.symm.trans chosenAt)
  have chosenKey : publishedOwner.view.kemPublic = chosen.1 := ownerKey.trans (congrArg Prod.fst samePair)
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds plainTyped mode work (project before) plainObserved plainSupport
  rw [projected, call.canonical] at accepted
  have sameRaw : call.raw = raw := Option.some.inj accepted
  rw [← sameRaw, call.decoded] at parsed
  have samePacket : call.packet = packet := Option.some.inj parsed
  have matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet)).map
      (fun keys => keys.2.pqKey) = some chosen.1 := by
    rw [samePacket, publicAcceptedKeys, Option.map_some, publicMatches, chosenKey]
  obtain ⟨ready, _authenticated, collected, stored, _reference, agreement, _verified, ciphertext, _atom, _readyAtom, _acceptedKeys⟩ :=
    RegistrationNativeSecretWordTargetRetainedPublic.accept_retained setup checks wire route sign nativeInput nativeInside
      selectedTarget.2.val pairs chosen.1 challenge outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar)
      call.packet call.first call.last session.val call.selected marker matching call.reached
  intro response found
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds plainTyped mode work
    (project before) plainObserved plainSupport
  rw [projected] at found
  obtain ⟨payload, member⟩ := RegistrationNativeSecretWordBuildChronology.original_build observed.2.1.transcript session.val response found
  rw [call.recorded] at member
  obtain ⟨buildFirst, buildLast, left, right, recorded, beforeBuild, built, afterBuild, encoded⟩ :=
    RegistrationNativeSecretWordBuildChronology.response setup checks wire route sign nativeInput nativeInside provider outer
      selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds call.raw call.packet session.val call.decoded
      prior called later ready stored payload response member
  have original : ready.agreement.pending.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge := by
    rw [agreement]
    exact ciphertext
  have firstPin := RegistrationNativeSecretWordServerPinSource.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds prior
  have acceptedPin := RegistrationNativeSecretWordServerPinSource.full setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds _ _ _ called
  have buildPin := RegistrationNativeSecretWordServerPinSource.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds beforeBuild
  have samePin : buildFirst.2.1.server.pin = before.1.1.server.pin := buildPin.trans (acceptedPin.trans firstPin)
  exact ⟨original ▸ encoded.1, by rw [samePin] at encoded; exact encoded.2⟩

end BeaconcryptCore.Computational.RegistrationNativeDesignatedResponse

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDesignatedResponse.encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDesignatedResponse.encoded
