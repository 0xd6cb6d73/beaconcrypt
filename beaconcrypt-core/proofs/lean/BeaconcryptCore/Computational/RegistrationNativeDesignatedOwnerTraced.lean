-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDesignatedResponse
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTracedFinish
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinishProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinPath
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPinSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath
import BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrdinal
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand

/-! Every broadly designated owner handle has its protected native installation at the exact successful linked finish. The original callback paths derive the challenge ciphertext and configured pin; no fresh-message claim or guessed private byte is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDesignatedOwnerTraced
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
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge
local notation "typedImpl" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetTracedSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordKemEarly.early

/-- A broadly designated owner handle has its same monitored successful finish and protected installation suffix. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (initReadback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (before : State n KemSK source)
    (initialCounter : before.1.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before))
    (actualPath : Path fullImpl (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (session : Fin budget.accept) (owner : Nat)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.owner owner) = some (session, target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val) :
    owner = target.2.val ∧ ∃ raw application pre post first last,
    ∃ ready : RegistrationNativeSecretWordMessage.BeaconReady,
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
  have encoded := RegistrationNativeDesignatedResponse.encoded setup checks wire route sign seed scalar pairs chosen challenge outer
    serverKeyId bounds mode work budget target bounded reserved chosenAt initReadback before initialCounter initialMarker ownersEmpty keysEmpty
    observed supported actualPath session (.owner owner) designated accepted
  obtain ⟨sameOwner, raw, publicPin, finished, packet, decoded, ciphertext⟩ :=
    RegistrationNativeOwnerLinkedFields.owner setup.source.crypto wire responseReadback serverKeyId budget observed.2.1.ledger.transcript owner
      session target.2 designated (PqxdhAcceptedRegistration.ciphertextArray challenge) before.1.1.server.pin.binding.identity_public_key encoded
  subst owner
  refine ⟨rfl, ?_⟩
  obtain ⟨application, pre, post, _plainFirst, _plainLast, recorded, _plainPrior, _plainCall, _plainLater⟩ :=
    RegistrationNativeSecretWordTargetOwnerCallPath.called setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
      serverKeyId bounds mode work (project before) projected projectedSupport projectedPath target.2.val raw finished
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
  exact ⟨raw, application, pre, post, first, last, ready,
    recorded, prior, fullCall, later, atom, realized, protectedHeads, bill⟩

/-- Every designated owner handle has its protected descriptor at the same final native installation ordinal. -/
theorem ordinal (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (before : State n KemSK source) (initialCounter : before.1.1.parsedAccepts = 0)
    (initialMarker : before.2.kem.2 = none) (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (candidate : MlKemSharedSecret)
    (counts : RegistrationNativeSecretWordTargetOrdinalBase.PrefixCounts setup checks wire route sign input inside provider outer
      target.2.val target.1.val publicPrekey serverKeyId bounds candidate before)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before))
    (actualPath : Path fullImpl (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (session : Fin budget.accept) (owner : Nat)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.owner owner) = some (session, target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val) :
    ∃ ordinal message, RegistrationNativeInstallOrdinals.At .beacon
        (observed.2.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
        observed.2.1.transcript ordinal message (.owner owner) ∧
      (∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  obtain ⟨sameOwner, raw, application, pre, post, first, last, ready,
      recorded, prior, _called, later, atom, _realized, protectedHeads, bill⟩ :=
    selected setup checks wire route sign seed scalar pairs chosen challenge outer serverKeyId bounds mode work budget target
      bounded reserved chosenAt readback responseReadback before initialCounter initialMarker ownersEmpty keysEmpty initialPin observed supported actualPath
      session owner designated accepted
  subst owner
  have count := RegistrationNativeSecretWordTargetOrdinalBase.prefix_count setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds candidate .beacon before pre first prior (counts .beacon pre first prior)
  obtain ⟨tail, suffix⟩ := RegistrationNativeSecretWordInstallMonotoneFull.path setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds .beacon later
  have own := bill .beacon
  simp only [ite_true] at own
  have joined : RegistrationNativeSecretWordInstallOrdinals.messages .beacon observed.2.2.1.2.events =
      RegistrationNativeSecretWordInstallOrdinals.messages .beacon first.2.1.2.events ++ ready.reference :: tail := by
    rw [suffix, own, List.append_assoc]
    rfl
  have handles : RegistrationNativeInstallOrdinals.handles .beacon observed.2.1.transcript =
      RegistrationNativeInstallOrdinals.handles .beacon pre ++ (.owner target.2.val) :: RegistrationNativeInstallOrdinals.handles .beacon post := by
    rw [recorded, RegistrationNativeInstallOrdinals.handles_append]
    rfl
  obtain ⟨ordinal, paired⟩ := RegistrationNativeSecretWordInstallWitness.at_append .beacon first.2.1.2.events observed.2.2.1.2.events pre
    observed.2.1.transcript ready.reference (.owner target.2.val) tail (RegistrationNativeInstallOrdinals.handles .beacon post) count joined handles
  refine ⟨ordinal, RegistrationNativeSecretWordMessage.eval candidate ready.reference,
    RegistrationNativeSecretWordInstallOrdinals.at_eval candidate .beacon _ _ ordinal ready.reference (.owner target.2.val) paired, ?_⟩
  intro bytes realized
  exact RegistrationNativeSelectiveHiddenDemand.selected_descriptor setup.joint setup.dh seed scalar candidate
    (setup.joint.staticDh seed (setup.dh.publicKey scalar)) ready.reference bytes atom protectedHeads realized

end BeaconcryptCore.Computational.RegistrationNativeDesignatedOwnerTraced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDesignatedOwnerTraced.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDesignatedOwnerTraced.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDesignatedOwnerTraced.ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDesignatedOwnerTraced.ordinal
