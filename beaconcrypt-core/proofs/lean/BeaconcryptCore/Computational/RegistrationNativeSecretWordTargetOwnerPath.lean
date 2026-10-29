-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerInputsPath
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinishProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath
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
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPath
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
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
  (outer : QueryImpl Combined ProbComp)
  (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
  (target : Fin budget.accept × Fin budget.capacity)
local notation "input" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "publicPrekey" => setup.dh.publicKey scalar
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordKemEarly.early

/-- An original selected owner APP win reaches its own actual successful completion with the challenge atom and protected first-DH descriptor. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (initReadback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before))
    (actualPath : Path fullImpl (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim observed)
    (ownerClaim : ∃ index guess entry owner, claim observed.1 = some (index, guess) ∧
      observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .owner owner) :
    ∃ index guess entry raw packet application pre post first last,
    ∃ current : RegistrationNativePublicOwners.Owner source,
    ∃ afterOwner : RegistrationBeaconReferenceCompiler.SelectedOwner source,
    ∃ preparedOwner : RegistrationBeaconReferenceCompiler.SelectedOwner source,
    ∃ ready : RegistrationNativeSecretWordMessage.BeaconReady,
    ∃ middle : RegistrationNativeSecretWordTargetServerExecution.Auxiliary n KemSK,
    ∃ afterEnv afterPrivate,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      entry.message = guess ∧ entry.handle = .owner target.2.val ∧
      observed.2.1.transcript = pre ++ (⟨.inl (.inr (.finish target.2.val raw)), some application⟩ : Entry) :: post ∧
      Path fullImpl (RegistrationNativeLedger.empty, before) pre first ∧
      (.ok (some application), last.2) ∈ support ((typedImpl (.inr (.finish target.2.val (some packet)))).run first.2) ∧
      Path fullImpl last post observed.2 ∧ first.2.1.beacons[target.2.val]? = some current ∧
      ready.reference.kem = RegistrationNativeSecretWord.Word.atom ∧
      (∃ key, input ready.reference = some key) ∧
      (∀ key, input ready.reference = some key → inside key.head = true) ∧
      ((.ok (some application), afterOwner), (afterEnv, afterPrivate)) ∈ support
        ((RegistrationNativeSecretWordTargetServerExecution.lower
          (RegistrationNativeSecretWordTargetServerExecution.localImpl setup wire route sign input inside provider outer false)
          ((RegistrationNativeSecretWordBeaconCompiler.complete setup.source current.view ready).run preparedOwner)).run middle) := by
  obtain ⟨index, guess, entry, raw, packet, application, pre, post, first, last,
      claimed, fresh, guessed, ownerHandle, recorded, prior, called, later, _decoded, ciphertext, _publicPin, currentPin⟩ :=
    RegistrationNativeSecretWordTargetOwnerInputsPath.selected setup checks wire route sign input inside pairs chosen challenge outer publicPrekey
      serverKeyId bounds mode work budget target bounded reserved chosenAt initReadback responseReadback claim before initialCounter initialMarker
      ownersEmpty keysEmpty observed supported actualPath winning ownerClaim
  have mask := RegistrationNativeSecretWordTargetOwnerPathState.path setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds prior
    (by rw [ownersEmpty]; exact RegistrationNativePublicOwnerMask.empty _ _)
  have aligned : RegistrationNativeSecretWordTargetAlignmentRun.Holds first.2 := by
    apply RegistrationNativeSecretWordTargetPath.preserves fullImpl
      (fun current => RegistrationNativeSecretWordTargetAlignmentRun.Holds current.2)
      (fun query current result previous reached => RegistrationNativeSecretWordTargetAlignmentRun.full_step_keeps setup checks wire route sign input inside
        target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey serverKeyId bounds query current previous result reached) prior
    simp only [RegistrationNativeSecretWordTargetAlignmentRun.Holds, ownersEmpty, keysEmpty]
    exact RegistrationNativeSecretWordTargetAlignment.empty
  have pending := RegistrationNativeSecretWordPendingPinPath.initialized setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds before ownersEmpty prior
  obtain ⟨current, afterOwner, preparedOwner, ready, middle, afterEnv, afterPrivate,
      found, atom, realized, protectedHeads, completed⟩ :=
    RegistrationNativeSecretWordTargetOwnerFinishProtected.finish setup checks wire route sign seed scalar target.2.val target.1.val pairs chosen.1 challenge outer
      packet application first.2 last.2 mask aligned
      (fun current found => by rw [currentPin current found]; exact initialPin)
      (fun current found => RegistrationNativeSecretWordPendingPin.pending current.view (pending target.2.val current found))
      ciphertext called
  exact ⟨index, guess, entry, raw, packet, application, pre, post, first, last, current, afterOwner, preparedOwner, ready, middle, afterEnv, afterPrivate,
    claimed, fresh, guessed, ownerHandle, recorded, prior, called, later, found, atom, realized, protectedHeads, completed⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPath.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPath.selected
