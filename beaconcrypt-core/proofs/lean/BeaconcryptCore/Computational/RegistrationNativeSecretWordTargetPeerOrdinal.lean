-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTraced
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTracedFinish
import BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinalBase

/-! The original broad peer target names its actual successful key-id-linked build, whose same pre-build Ready is retained from the same canonical accept path. Earlier builds with other key ids are not identified with this designated response. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerOrdinal
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

/-- The original good peer claim is paired with its own protected atom at a final evaluated installation ordinal. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (candidate : MlKemSharedSecret)
    (counts : RegistrationNativeSecretWordTargetOrdinalBase.PrefixCounts setup checks wire route sign nativeInput nativeInside provider outer
      selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds candidate before)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (actualPath : Path full (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim observed)
    (peerClaim : ∃ index guess entry keyId, claim observed.1 = some (index, guess) ∧
      observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .peer keyId) :
    ∃ index guess entry ordinal message,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧ entry.message = guess ∧
      message.kem = Word.atom ∧ (∀ key, nativeInput message = some key → nativeInside key.head = true) ∧
      RegistrationNativeInstallOrdinals.At .server
        (observed.2.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) observed.2.1.transcript
        ordinal (RegistrationNativeSecretWordMessage.eval candidate message) entry.handle := by
  obtain ⟨index, guess, entry, keyId, session, payload, response, ready, first, last, pre, post,
      claimed, fresh, handle, guessed, responseKey, recorded, prior, called, later, stored, atom, protectedHeads⟩ :=
    RegistrationNativeSecretWordTargetPeerTraced.selected setup checks wire route sign seed scalar pairs chosen challenge outer serverKeyId bounds mode work budget
      selectedTarget bounded reserved chosenAt readback claim before initialCounter initialMarker ownersEmpty keysEmpty observed supported actualPath winning peerClaim
  have rawCall := called
  rw [RegistrationNativeTargetLedgerCore.run, support_map] at rawCall
  obtain ⟨⟨reply, reached⟩, actualRaw, returned⟩ := rawCall
  have replyEq : reply = some response := congrArg Prod.fst returned
  have stateEq : reached = last.2 := congrArg (fun result => result.2.2) returned
  subst reply
  rw [stateEq] at actualRaw
  have typedCall := RegistrationNativeTargetRawSuccess.build wire typed session.val payload response first.2 last.2 actualRaw
  have own := RegistrationNativeSecretWordTargetPeerTracedFinish.build setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) .server session.val (RegistrationNativeRawAdapter.application payload)
    response.keyId response.serialized ready first.2 last.2 stored typedCall
  simp only [ite_true] at own
  have count := RegistrationNativeSecretWordTargetOrdinalBase.prefix_count setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds candidate .server before pre first prior (counts .server pre first prior)
  obtain ⟨tail, suffix⟩ := RegistrationNativeSecretWordInstallMonotoneFull.path setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds .server later
  have joined : RegistrationNativeSecretWordInstallOrdinals.messages .server observed.2.2.1.2.events =
      RegistrationNativeSecretWordInstallOrdinals.messages .server first.2.1.2.events ++ ready.reference :: tail := by
    rw [suffix, own, List.append_assoc]
    rfl
  have handles : RegistrationNativeInstallOrdinals.handles .server observed.2.1.transcript =
      RegistrationNativeInstallOrdinals.handles .server pre ++ entry.handle :: RegistrationNativeInstallOrdinals.handles .server post := by
    rw [handle, recorded, RegistrationNativeInstallOrdinals.handles_append]
    simp only [RegistrationNativeInstallOrdinals.handles, List.filterMap_cons]
    rw [responseKey]
  obtain ⟨ordinal, paired⟩ := RegistrationNativeSecretWordInstallWitness.at_append .server first.2.1.2.events observed.2.2.1.2.events pre
    observed.2.1.transcript ready.reference entry.handle tail (RegistrationNativeInstallOrdinals.handles .server post) count joined handles
  exact ⟨index, guess, entry, ordinal, ready.reference, claimed, fresh, guessed, atom, protectedHeads,
    RegistrationNativeSecretWordInstallOrdinals.at_eval candidate .server _ _ ordinal ready.reference entry.handle paired⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerOrdinal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerOrdinal.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerOrdinal.selected
