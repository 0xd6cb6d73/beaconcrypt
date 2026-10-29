-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected

/-! The original canonical peer APP selectedTarget has the same retained atom root in the protected first-DH slice. Every identification is taken from its actual original call, verified packet, published selected prekey and transported public equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeer
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetCall (Call)
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

/-- Actual canonical peer success supplies its same retained successful atom reference, and every realized descriptor key is protected. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim observed)
    (peerClaim : ∃ index guess entry keyId, claim observed.1 = some (index, guess) ∧
      observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .peer keyId) :
    ∃ index guess entry, ∃ session : Fin budget.accept,
      ∃ call : Call (State n KemSK source) typed (fun current => current.1.parsedAccepts)
        wire selectedTarget.1.val observed.2.1.transcript session.val,
      ∃ ready : RegistrationNativeSecretWordMessage.ServerReady,
      ∃ collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      entry.message = guess ∧ call.last.1.server.sessions[session.val]? = some (some ready) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧ ready.reference.kem = Word.atom ∧
      collected.plain.verified.keys.prekey = setup.dh.publicKey scalar ∧
      ∀ key, nativeInput ready.reference = some key → nativeInside key.head = true := by
  have original := RegistrationNativePrekeyEvents.target_original setup.source.crypto wire serverKeyId budget selectedTarget claim observed winning
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, _marker, _matching,
      ready, _authenticated, collected, stored, reference, _verified, _ciphertext, _atom, readyAtom, acceptedKeys⟩ :=
    RegistrationNativeSecretWordTargetCanonicalRetained.selected_retained setup checks wire route sign nativeInput nativeInside pairs chosen challenge
      outer (setup.dh.publicKey scalar) serverKeyId bounds mode work budget selectedTarget bounded reserved chosenAt readback claim before initialCounter initialMarker
      ownersEmpty keysEmpty observed supported original
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
  refine ⟨index, guess, entry, session, call, ready, collected, claimed, fresh, guessed, stored, reference, readyAtom, prekey, ?_⟩
  intro key realized
  rw [reference] at realized
  exact RegistrationNativeSecretWordTargetProtected.server_inside setup seed scalar RegistrationNativeSecretWordMessage.zero collected prekey key realized
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeer.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeer.selected
