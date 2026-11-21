-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrdinal
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerOrdinal
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger
import BeaconcryptCore.Computational.RegistrationNativeInstallTarget

/-! A good original claim has a selected native descriptor at the same final role ordinal as its claimed physical handle. Owner and peer provenance are derived at their actual monitored callback cuts; only the final evaluated trace and original public transcript appear in the conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinal
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

/-- A good original target has a selected descriptor paired with its claimed handle in the final evaluated native trace. -/
theorem selected_of_counts (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (candidate : MlKemSharedSecret)
    (counts : RegistrationNativeSecretWordTargetOrdinalBase.PrefixCounts setup checks wire route sign nativeInput nativeInside provider outer
      selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds candidate before)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (actualPath : Path full (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim observed) :
    ∃ index guess entry role ordinal message,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧ entry.message = guess ∧
      RegistrationNativeInstallOrdinals.At role
        (observed.2.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) observed.2.1.transcript
        ordinal message entry.handle ∧
      (∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  have good := winning
  obtain ⟨index, guess, entry, _session, claimed, fresh, _designated, _accepted, _guessed, _pinned⟩ := winning
  cases handle : entry.handle with
  | owner owner =>
      have ownerClaim : ∃ index guess entry owner, claim observed.1 = some (index, guess) ∧
          observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .owner owner :=
        ⟨index, guess, entry, owner, claimed, fresh, handle⟩
      obtain ⟨actualIndex, actualGuess, actualEntry, ordinal, message, actualClaimed, actualFresh, actualGuessed, atom, protectedHeads, paired⟩ :=
        RegistrationNativeSecretWordTargetOwnerOrdinal.selected setup checks wire route sign seed scalar pairs chosen challenge outer
          serverKeyId bounds mode work budget selectedTarget bounded reserved chosenAt readback responseReadback claim before initialCounter initialMarker
          ownersEmpty keysEmpty initialPin candidate counts observed supported actualPath good ownerClaim
      refine ⟨actualIndex, actualGuess, actualEntry, .beacon, ordinal, RegistrationNativeSecretWordMessage.eval candidate message,
        actualClaimed, actualFresh, actualGuessed, paired, ?_⟩
      intro bytes realized
      exact RegistrationNativeSelectiveHiddenDemand.selected_descriptor setup.joint setup.dh seed scalar candidate
        (setup.joint.staticDh seed (setup.dh.publicKey scalar)) message bytes atom protectedHeads realized
  | peer keyId =>
      have peerClaim : ∃ index guess entry keyId, claim observed.1 = some (index, guess) ∧
          observed.2.1.ledger.fresh[index]? = some entry ∧ entry.handle = .peer keyId :=
        ⟨index, guess, entry, keyId, claimed, fresh, handle⟩
      obtain ⟨actualIndex, actualGuess, actualEntry, ordinal, message, actualClaimed, actualFresh, actualGuessed, atom, protectedHeads, paired⟩ :=
        RegistrationNativeSecretWordTargetPeerOrdinal.selected setup checks wire route sign seed scalar pairs chosen challenge outer
          serverKeyId bounds mode work budget selectedTarget bounded reserved chosenAt readback claim before initialCounter initialMarker
          ownersEmpty keysEmpty candidate counts observed supported actualPath good peerClaim
      refine ⟨actualIndex, actualGuess, actualEntry, .server, ordinal, RegistrationNativeSecretWordMessage.eval candidate message,
        actualClaimed, actualFresh, actualGuessed, paired, ?_⟩
      intro bytes realized
      exact RegistrationNativeSelectiveHiddenDemand.selected_descriptor setup.joint setup.dh seed scalar candidate
        (setup.joint.staticDh seed (setup.dh.publicKey scalar)) message bytes atom protectedHeads realized

/-- Empty actual startup chronology discharges the complete original good target's selected-installation receipt. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : State n KemSK source)
    (initialCounter : before.1.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (candidate : MlKemSharedSecret)
    (initialTrace : before.1.2.events = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (actualPath : Path full (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim observed) :
    RegistrationNativeInstallTarget.Claimed claim observed.1 observed.2.1
      (observed.2.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (fun message => ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  exact selected_of_counts setup checks wire route sign seed scalar pairs chosen challenge outer serverKeyId bounds mode work budget selectedTarget
    bounded reserved chosenAt readback responseReadback claim before initialCounter initialMarker ownersEmpty keysEmpty initialPin candidate
    (RegistrationNativeSecretWordInstallLedger.prefix_counts setup checks wire route sign nativeInput nativeInside provider outer
      selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) candidate serverKeyId bounds before initialTrace)
    observed supported actualPath winning

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinal.selected_of_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinal.selected_of_counts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinal.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinal.selected
