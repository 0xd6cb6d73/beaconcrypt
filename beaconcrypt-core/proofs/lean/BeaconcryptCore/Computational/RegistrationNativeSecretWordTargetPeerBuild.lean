-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetResponsePath
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
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerBuild
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
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
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign nativeInput nativeInside provider outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State n KemSK source

/-- The actual canonical broad peer win supplies its same designated successful build and protected atom Ready at that build's actual chronological source cut. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
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
      buildFirst.2.1.server.sessions[session.val]? = some (some ready) ∧ ready.reference.kem = Word.atom ∧
      ∀ key, nativeInput ready.reference = some key → nativeInside key.head = true := by
  have original := RegistrationNativePrekeyEvents.target_original setup.source.crypto wire serverKeyId budget selectedTarget claim observed winning
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, _marker, _matching,
      ready, _authenticated, collected, stored, reference, _agreement, _verified, _ciphertext, _atom, readyAtom, acceptedKeys,
      firstLedger, lastLedger, prior, called, later, _firstBuild⟩ :=
    RegistrationNativeSecretWordTargetResponsePath.selected_retained setup checks wire route sign nativeInput nativeInside pairs chosen challenge
      outer (setup.dh.publicKey scalar) serverKeyId bounds mode work budget selectedTarget bounded reserved chosenAt readback claim before initialCounter initialMarker
      ownersEmpty keysEmpty observed supported actualPath original
  obtain ⟨otherIndex, otherGuess, otherEntry, keyId, otherClaimed, otherFresh, peerHandle⟩ := peerClaim
  have pair := Option.some.inj (otherClaimed.symm.trans claimed)
  have sameIndex : otherIndex = index := congrArg Prod.fst pair
  subst otherIndex
  have sameEntry := Option.some.inj (otherFresh.symm.trans fresh)
  subst otherEntry
  have pinned := RegistrationNativePrekeyEvents.target_pinned setup.source.crypto wire serverKeyId budget selectedTarget claim observed winning index guess entry claimed fresh
  rw [peerHandle] at designated pinned
  have prekey := RegistrationNativeSecretWordTargetProtected.call_prekey setup checks wire route sign nativeInput nativeInside
    pairs chosen challenge outer (setup.dh.publicKey scalar) serverKeyId bounds mode work budget selectedTarget readback before ownersEmpty observed supported
    session call keyId pinned designated collected acceptedKeys
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId budget observed.2.1.ledger.transcript (.peer keyId) (session, selectedTarget.2) designated
  obtain ⟨response, _raw, _accepted, _keys, linked, _rawFound, _acceptedFound, _keysFound, _ownerBound, _published⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId keyId
      observed.2.1.ledger.transcript session.val selectedTarget.2.val plain
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  rw [projected] at linked
  obtain ⟨sameKey, payload, member⟩ := RegistrationNativeLinkedBuild.original observed.2.1.transcript keyId session.val response linked
  rw [call.recorded] at member
  obtain ⟨buildFirst, buildLast, left, right, recorded, beforeBuild, built, afterBuild, _encoded⟩ :=
    RegistrationNativeSecretWordBuildChronology.response setup checks wire route sign nativeInput nativeInside provider outer
      selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds call.raw call.packet session.val call.decoded
      prior called later ready stored payload response member
  obtain ⟨actual, selectedReady, _encoded⟩ := RegistrationNativeSecretWordResponseLedger.full setup checks wire route sign nativeInput nativeInside
    provider outer selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds session.val payload response buildFirst buildLast built
  have slots := RegistrationNativeSecretWordSessionSlotsSource.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds beforeBuild
  have equal := slots.2 session.val (List.getElem?_eq_some_iff.mp stored).1 actual selectedReady
  have same : actual = ready := Option.some.inj (Option.some.inj (equal.symm.trans stored))
  subst actual
  have throughAccept : Path full (firstLedger, call.first)
      [⟨.inl (.inr (.accept call.raw)), some session.val⟩] (lastLedger, call.last) :=
    .cons _ _ _ _ _ [] called (.nil _)
  have buildPrefix := RegistrationNativeSecretWordTargetPathConcat.append full
    (RegistrationNativeSecretWordTargetPathConcat.append full prior throughAccept) beforeBuild
  refine ⟨index, guess, entry, keyId, session, payload, response, ready, buildFirst, buildLast,
    (call.pre ++ [⟨.inl (.inr (.accept call.raw)), some session.val⟩]) ++ left, right,
    claimed, fresh, peerHandle, guessed, sameKey, ?_, buildPrefix, built, afterBuild, selectedReady, readyAtom, ?_⟩
  · apply call.recorded.trans
    rw [recorded]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · intro key realized
    rw [reference] at realized
    exact RegistrationNativeSecretWordTargetProtected.server_inside setup seed scalar RegistrationNativeSecretWordMessage.zero collected prekey key realized

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerBuild.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerBuild.selected
