-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalTraced
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetainedPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
import BeaconcryptCore.Computational.RegistrationNativeLinkedBuild

/-! The original broad peer target names its actual successful key-id-linked build, whose same pre-build Ready is retained from the same canonical accept path. Earlier builds with other key ids are not identified with this designated response. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTraced
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
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge
local notation "plainTyped" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign nativeInput nativeInside provider outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar)
local notation "typed" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign nativeInput nativeInside provider outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State n KemSK source

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetTracedSource.typed RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordKemEarly.early

/-- The actual canonical broad peer win supplies its same designated successful build and protected atom Ready at that build's actual chronological source cut. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (actualPath : Path full (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim observed)
    (peerClaim : ∃ index guess entry keyId, claim observed.1 = some (index, guess) ∧
      observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .peer keyId) :
    ∃ index guess entry keyId, ∃ session : Fin budget.accept,
    ∃ payload response, ∃ ready : RegistrationNativeSecretWordMessage.ServerReady,
    ∃ (buildFirst buildLast : FullState) (left right : List RegistrationNativeInterface.Entry),
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      entry.handle = .peer keyId ∧ entry.message = guess ∧ response.keyId = keyId ∧
      observed.2.1.transcript = left ++ ⟨.inl (.inr (.build session.val payload)), some response⟩ :: right ∧
      Path full (RegistrationNativeLedger.empty, before) left buildFirst ∧
      (some response, buildLast) ∈ support ((full (.inl (.inr (.build session.val payload)))).run buildFirst) ∧
      Path full buildLast right observed.2 ∧
      buildFirst.2.1.1.server.sessions[session.val]? = some (some ready) ∧ ready.reference.kem = Word.atom ∧
      ∀ key, nativeInput ready.reference = some key → nativeInside key.head = true := by
  let plainObserved := (observed.1, (observed.2.1, project observed.2.2))
  have plainSupport := Set.mem_image_of_mem (Prod.map id (Prod.map id project)) supported
  rw [← support_map, RegistrationNativeSecretWordTargetTracedPath.erase_run setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode work before] at plainSupport
  have original := RegistrationNativePrekeyEvents.target_original setup.source.crypto wire serverKeyId budget selectedTarget claim observed winning
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker,
      traceFirst, traceLast, firstEq, lastEq, priorTrace, calledTrace, laterTrace⟩ :=
    RegistrationNativeSecretWordTargetChronologicalTraced.selected_call setup checks wire route sign nativeInput nativeInside pairs chosen.1 challenge
      outer (setup.dh.publicKey scalar) serverKeyId bounds mode work budget selectedTarget claim before initialCounter initialMarker observed actualPath original
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
      entry.handle (session, selectedTarget.2) designated
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
  obtain ⟨ready, _authenticated, collected, stored, reference, _agreement, _verified, _ciphertext, _atom, readyAtom, acceptedKeys⟩ :=
    RegistrationNativeSecretWordTargetRetainedPublic.accept_retained setup checks wire route sign nativeInput nativeInside
      selectedTarget.2.val pairs chosen.1 challenge outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar)
      call.packet call.first call.last session.val call.selected marker matching call.reached
  obtain ⟨otherIndex, otherGuess, otherEntry, keyId, otherClaimed, otherFresh, peerHandle⟩ := peerClaim
  have pair := Option.some.inj (otherClaimed.symm.trans claimed)
  have sameIndex : otherIndex = index := congrArg Prod.fst pair
  subst otherIndex
  have sameEntry := Option.some.inj (otherFresh.symm.trans fresh)
  subst otherEntry
  have pinned := RegistrationNativePrekeyEvents.target_pinned setup.source.crypto wire serverKeyId budget selectedTarget claim observed winning index guess entry claimed fresh
  rw [peerHandle] at designated pinned
  have prekey := RegistrationNativeSecretWordTargetProtected.call_prekey setup checks wire route sign nativeInput nativeInside
    pairs chosen challenge outer (setup.dh.publicKey scalar) serverKeyId bounds mode work budget selectedTarget readback (project before) ownersEmpty plainObserved plainSupport
    session call keyId pinned designated collected acceptedKeys
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId budget observed.2.1.ledger.transcript (.peer keyId) (session, selectedTarget.2) designated
  obtain ⟨response, _raw, _accepted, _keys, linked, _rawFound, _acceptedFound, _keysFound, _ownerBound, _published⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId keyId
      observed.2.1.ledger.transcript session.val selectedTarget.2.val plain
  have ledger := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  rw [ledger] at linked
  obtain ⟨sameKey, payload, member⟩ := RegistrationNativeLinkedBuild.original observed.2.1.transcript keyId session.val response linked
  rw [call.recorded] at member
  obtain ⟨_untracedFirst, _untracedLast, left, right, recorded, _untracedPrior, _untracedBuilt, _untracedLater, _encoded⟩ :=
    RegistrationNativeSecretWordBuildChronology.response setup checks wire route sign nativeInput nativeInside provider outer
      selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds call.raw call.packet session.val call.decoded
      prior called later ready stored payload response member
  obtain ⟨buildFirst, buildLast, beforeBuild, built, afterBuild⟩ := RegistrationNativeSecretWordTargetPath.split full laterTrace left _ right recorded
  have beforeSource := RegistrationNativeSecretWordTargetTracedPath.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds beforeBuild
  have builtSource := Set.mem_image_of_mem (Prod.map id (Prod.map id project)) built
  rw [← support_map, RegistrationNativeSecretWordTargetTracedPath.full setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds] at builtSource
  simp only [Prod.map_def, id_eq] at beforeSource builtSource
  rw [← lastEq] at beforeSource
  obtain ⟨actual, selectedReady, _encoded⟩ := RegistrationNativeSecretWordResponseLedger.full setup checks wire route sign nativeInput nativeInside
    provider outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds session.val payload response
    (buildFirst.1, project buildFirst.2) (buildLast.1, project buildLast.2) builtSource
  have slots := RegistrationNativeSecretWordSessionSlotsSource.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds beforeSource
  have equal := slots.2 session.val (List.getElem?_eq_some_iff.mp stored).1 actual selectedReady
  have same : actual = ready := Option.some.inj (Option.some.inj (equal.symm.trans stored))
  subst actual
  have throughAccept : Path full traceFirst [⟨.inl (.inr (.accept call.raw)), some session.val⟩] traceLast :=
    .cons _ _ _ _ _ [] calledTrace (.nil _)
  have buildPrefix := RegistrationNativeSecretWordTargetPathConcat.append full
    (RegistrationNativeSecretWordTargetPathConcat.append full priorTrace throughAccept) beforeBuild
  refine ⟨index, guess, entry, keyId, session, payload, response, ready, buildFirst, buildLast,
    (call.pre ++ [⟨.inl (.inr (.accept call.raw)), some session.val⟩]) ++ left, right,
    claimed, fresh, peerHandle, guessed, sameKey, ?_, buildPrefix, built, afterBuild, selectedReady, readyAtom, ?_⟩
  · apply call.recorded.trans
    rw [recorded]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · intro key realized
    rw [reference] at realized
    exact RegistrationNativeSecretWordTargetProtected.server_inside setup seed scalar RegistrationNativeSecretWordMessage.zero collected prekey key realized
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTraced
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTraced.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTraced.selected
