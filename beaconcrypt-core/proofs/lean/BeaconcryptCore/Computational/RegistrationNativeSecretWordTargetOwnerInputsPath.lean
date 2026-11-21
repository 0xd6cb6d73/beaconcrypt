-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetResponsePath
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPinSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath
import BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents

/-! The original owner APP designation supplies its same successful finish callback, actual challenge ciphertext and actual current configured Server pin. The selected accept, linked response, successful finish and original public pin summary are connected through their literal full-ledger source paths. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerInputsPath
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeInterface (Entry)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
  (outer : QueryImpl Combined ProbComp) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
  (target : Fin budget.accept × Fin budget.capacity)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordKemEarly.early

/-- The actual original selected owner call inherits the challenge ciphertext and its own configured pin from the same linked response and public designation. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (initReadback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before))
    (actualPath : Path fullImpl (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim observed)
    (ownerClaim : ∃ index guess entry owner, claim observed.1 = some (index, guess) ∧
      observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .owner owner) :
    ∃ index guess entry raw packet application pre post first last,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      entry.message = guess ∧ entry.handle = .owner target.2.val ∧
      observed.2.1.transcript = pre ++ (⟨.inl (.inr (.finish target.2.val raw)), some application⟩ : Entry) :: post ∧
      Path fullImpl (RegistrationNativeLedger.empty, before) pre first ∧
      (.ok (some application), last.2) ∈ support ((typedImpl (.inr (.finish target.2.val (some packet)))).run first.2) ∧
      Path fullImpl last post observed.2 ∧
      RegistrationNativeWire.readResponse wire raw = some packet ∧
      packet.public.kem_cipher_text = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
      (PqxdhDeploymentTranscript.summarize observed.2.1.ledger.transcript).owners[target.2.val]? =
        some (before.1.server.pin.binding.identity_public_key, serverKeyId) ∧
      ∀ current, first.2.1.beacons[target.2.val]? = some current →
        current.view.pin.binding.identity_public_key = before.1.server.pin.binding.identity_public_key := by
  have original := RegistrationNativePrekeyEvents.target_original setup.source.crypto wire serverKeyId budget target claim observed winning
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, _marker, _matching,
      _ready, _authenticated, _collected, _stored, _reference, _agreement, _verified, _ciphertext,
      _atom, _readyAtom, _acceptedKeys, firstLedger, lastLedger, prior, called, _later, responses⟩ :=
    RegistrationNativeSecretWordTargetResponsePath.selected_retained setup checks wire route sign input inside pairs chosen challenge
      outer publicPrekey serverKeyId bounds mode work budget target bounded reserved chosenAt initReadback claim before initialCounter initialMarker
      ownersEmpty keysEmpty observed supported actualPath original
  obtain ⟨otherIndex, otherGuess, otherEntry, owner, otherClaimed, otherFresh, ownerHandle⟩ := ownerClaim
  have pair := Option.some.inj (otherClaimed.symm.trans claimed)
  have sameIndex : otherIndex = index := congrArg Prod.fst pair
  subst otherIndex
  have sameEntry := Option.some.inj (otherFresh.symm.trans fresh)
  subst otherEntry
  rw [ownerHandle] at designated
  have encoded : ∀ response, PqxdhDeploymentTranscript.buildOf observed.2.1.ledger.transcript session.val = some response →
      RegistrationNativeResponseCiphertext.EncodedFrom wire.encodeResponse (PqxdhAcceptedRegistration.ciphertextArray challenge) response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom wire.encodeResponse before.1.server.pin.binding.identity_public_key response.serialized := by
    intro response built
    obtain ⟨_payload, buildFirst, _buildLast, _left, _right, _recorded, beforeBuild, _built, _afterBuild, ciphertext, identity⟩ := responses response built
    have firstPin := RegistrationNativeSecretWordServerPinSource.path setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey serverKeyId bounds prior
    have acceptedPin := RegistrationNativeSecretWordServerPinSource.full setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey serverKeyId bounds _ _ _ called
    have buildPin := RegistrationNativeSecretWordServerPinSource.path setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey serverKeyId bounds beforeBuild
    have samePin : buildFirst.2.1.server.pin = before.1.server.pin := buildPin.trans (acceptedPin.trans firstPin)
    exact ⟨ciphertext, by rw [samePin] at identity; exact identity⟩
  obtain ⟨sameOwner, raw, summaryPin, finished, packet, decoded, ciphertext⟩ :=
    RegistrationNativeOwnerLinkedFields.owner setup.source.crypto wire responseReadback serverKeyId budget observed.2.1.ledger.transcript owner session target.2 designated
      (PqxdhAcceptedRegistration.ciphertextArray challenge) before.1.server.pin.binding.identity_public_key encoded
  subst owner
  have originalSummary := summaryPin
  obtain ⟨application, pre, post, first, last, recorded, beforeFinish, finished, afterFinish⟩ :=
    RegistrationNativeSecretWordTargetOwnerCallPath.called setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
      serverKeyId bounds mode work before observed supported actualPath target.2.val raw finished
  refine ⟨index, guess, entry, raw, packet, application, pre, post, first, last,
    claimed, fresh, guessed, ownerHandle, recorded, beforeFinish, ?_, afterFinish, decoded, ciphertext, originalSummary, ?_⟩
  · rw [decoded] at finished
    exact finished
  · intro current found
    have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typedImpl mode work before observed supported
    rw [projected, recorded] at summaryPin
    have currentPin := RegistrationNativeSecretWordOwnerPinPath.owner setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
      serverKeyId bounds before ownersEmpty pre ((⟨.inl (.inr (.finish target.2.val raw)), some application⟩ : Entry) :: post)
      first beforeFinish target.2.val current found before.1.server.pin.binding.identity_public_key serverKeyId summaryPin
    exact congrArg (fun binding => binding.identity_public_key) currentPin

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerInputsPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerInputsPath.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerInputsPath.selected
