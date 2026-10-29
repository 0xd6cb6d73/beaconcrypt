-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerInputsPath
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTracedFinish
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
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
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTraced
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetTracedSource (State project)
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
local notation "typedImpl" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetTracedSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordKemEarly.early

/-- Original selected owner success has its own same monitored callback and protected successful installation suffix. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (initReadback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before))
    (actualPath : Path fullImpl (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim observed)
    (ownerClaim : ∃ index guess entry owner, claim observed.1 = some (index, guess) ∧
      observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .owner owner) :
    ∃ index guess entry raw application pre post first last,
    ∃ ready : RegistrationNativeSecretWordMessage.BeaconReady,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      entry.message = guess ∧ entry.handle = .owner target.2.val ∧
      observed.2.1.transcript = pre ++ (⟨.inl (.inr (.finish target.2.val raw)), some application⟩ : Entry) :: post ∧
      Path fullImpl (RegistrationNativeLedger.empty, before) pre first ∧
      (some application, last) ∈ support ((fullImpl (.inl (.inr (.finish target.2.val raw)))).run first) ∧
      Path fullImpl last post observed.2 ∧
      ready.reference.kem = RegistrationNativeSecretWord.Word.atom ∧
      (∃ key, input ready.reference = some key) ∧
      (∀ key, input ready.reference = some key → inside key.head = true) ∧
      ∀ role, RegistrationNativeSecretWordInstallOrdinals.messages role last.2.1.2.events =
        RegistrationNativeSecretWordInstallOrdinals.messages role first.2.1.2.events ++
          if role = .beacon then [ready.reference] else [] := by
  let projected := (observed.1, (observed.2.1, project observed.2.2))
  have projectedSupport := Set.mem_image_of_mem (Prod.map id (Prod.map id project)) supported
  rw [← support_map, RegistrationNativeSecretWordTargetTracedPath.erase_run setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds mode work before] at projectedSupport
  have projectedPath := RegistrationNativeSecretWordTargetTracedPath.path setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds actualPath
  obtain ⟨index, guess, entry, raw, packet, application, pre, post, _oldFirst, _oldLast,
      claimed, fresh, guessed, ownerHandle, recorded, _oldPrior, _oldCall, _oldLater, decoded, ciphertext, publicPin, _oldPin⟩ :=
    RegistrationNativeSecretWordTargetOwnerInputsPath.selected setup checks wire route sign input inside pairs chosen challenge outer publicPrekey
      serverKeyId bounds mode work budget target bounded reserved chosenAt initReadback responseReadback claim (project before) initialCounter initialMarker
      ownersEmpty keysEmpty projected projectedSupport projectedPath winning ownerClaim
  obtain ⟨first, last, prior, fullCall, later⟩ := RegistrationNativeSecretWordTargetPath.split fullImpl actualPath pre _ post recorded
  have actualRaw := fullCall
  rw [RegistrationNativeTargetLedgerCore.run, support_map] at actualRaw
  obtain ⟨⟨reply, reached⟩, rawCall, equal⟩ := actualRaw
  have replyEq : reply = some application := congrArg Prod.fst equal
  have stateEq : reached = last.2 := congrArg (fun result => result.2.2) equal
  subst reply
  rw [stateEq] at rawCall
  have typedCall : (.ok (some application), last.2) ∈ support ((typedImpl (.inr (.finish target.2.val (some packet)))).run first.2) := by
    simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
      simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at rawCall
    obtain ⟨⟨reply, after⟩, called, returned⟩ := rawCall
    cases actual : reply with
    | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at returned
    | ok result =>
        simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at returned
        obtain ⟨rfl, rfl⟩ := returned
        rw [decoded] at called
        simpa only [actual] using called
  have sourcePrior := RegistrationNativeSecretWordTargetTracedPath.path setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds prior
  have mask := RegistrationNativeSecretWordTargetOwnerPathState.path setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds sourcePrior
    (by simp only [Prod.map_def, id_eq, project, ownersEmpty]; exact RegistrationNativePublicOwnerMask.empty _ _)
  have aligned : RegistrationNativeSecretWordTargetAlignmentRun.Holds (project first.2) := by
    apply RegistrationNativeSecretWordTargetPath.preserves _
      (fun current => RegistrationNativeSecretWordTargetAlignmentRun.Holds current.2)
      (fun query current result previous reached => RegistrationNativeSecretWordTargetAlignmentRun.full_step_keeps setup checks wire route sign input inside
        target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey serverKeyId bounds query current previous result reached) sourcePrior
    simp only [RegistrationNativeSecretWordTargetAlignmentRun.Holds, Prod.map_def, id_eq, project, ownersEmpty, keysEmpty]
    exact RegistrationNativeSecretWordTargetAlignment.empty
  have pending := RegistrationNativeSecretWordPendingPinPath.initialized setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds (project before) ownersEmpty sourcePrior
  obtain ⟨ready, atom, realized, protectedHeads, bill⟩ :=
    RegistrationNativeSecretWordTargetOwnerTracedFinish.finish setup checks wire route sign seed scalar target.2.val target.1.val pairs chosen.1 challenge outer
      packet application first.2 last.2 mask aligned
      (fun current found => by
        have finalProjection := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typedImpl mode work before observed supported
        rw [finalProjection, recorded] at publicPin
        have pin := RegistrationNativeSecretWordOwnerPinPath.owner setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
          serverKeyId bounds (project before) ownersEmpty pre ((⟨.inl (.inr (.finish target.2.val raw)), some application⟩ : Entry) :: post)
          (first.1, project first.2) sourcePrior target.2.val current found before.1.1.server.pin.binding.identity_public_key serverKeyId publicPin
        rw [congrArg (fun binding => binding.identity_public_key) pin]
        exact initialPin)
      (fun current found => RegistrationNativeSecretWordPendingPin.pending current.view (pending target.2.val current found))
      ciphertext typedCall
  exact ⟨index, guess, entry, raw, application, pre, post, first, last, ready,
    claimed, fresh, guessed, ownerHandle, recorded, prior, fullCall, later, atom, realized, protectedHeads, bill⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTraced
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTraced.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTraced.selected
