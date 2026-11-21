-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDesignatedOwnerTraced
import BeaconcryptCore.Computational.RegistrationNativeDesignatedPeerTraced
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger
/-! Arbitrary publicly designated handles receive same-run protected installation receipts, independent of any fresh claim. Both peer and owner callbacks are connected to the exact canonical accepted entry; the empty actual chronology supplies prefix counts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleOrdinal
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

/-- An arbitrary broadly designated handle, with the retained public pin equality, has a protected descriptor paired with its final installation ordinal. -/
theorem of_counts (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
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
    (session : Fin budget.accept) (handle : PqxdhDeploymentInterface.Handle)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript handle = some (session, target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId observed.2.1.ledger.transcript handle) :
    ∃ role ordinal message, RegistrationNativeInstallOrdinals.At role
        (observed.2.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
        observed.2.1.transcript ordinal message handle ∧
      (∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  cases handle with
  | peer keyId =>
      obtain ⟨ordinal, message, paired, selected⟩ := RegistrationNativeDesignatedPeerTraced.ordinal setup checks wire route sign seed scalar pairs chosen challenge outer
        serverKeyId bounds mode work budget target bounded reserved chosenAt readback before initialCounter initialMarker ownersEmpty keysEmpty candidate counts
        observed supported actualPath session keyId designated accepted pinned
      exact ⟨.server, ordinal, message, paired, selected⟩
  | owner index =>
      obtain ⟨ordinal, message, paired, selected⟩ := RegistrationNativeDesignatedOwnerTraced.ordinal setup checks wire route sign seed scalar pairs chosen challenge outer
        serverKeyId bounds mode work budget target bounded reserved chosenAt readback responseReadback before initialCounter initialMarker ownersEmpty keysEmpty initialPin
        candidate counts observed supported actualPath session index designated accepted
      exact ⟨.beacon, ordinal, message, paired, selected⟩

/-- Empty actual startup chronology discharges the prefix count invariant for arbitrary designated handles. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (before : State n KemSK source) (initialCounter : before.1.1.parsedAccepts = 0)
    (initialMarker : before.2.kem.2 = none) (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (candidate : MlKemSharedSecret) (initialTrace : before.1.2.events = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before))
    (actualPath : Path fullImpl (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (session : Fin budget.accept) (handle : PqxdhDeploymentInterface.Handle)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript handle = some (session, target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId observed.2.1.ledger.transcript handle) :
    ∃ role ordinal message, RegistrationNativeInstallOrdinals.At role
        (observed.2.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
        observed.2.1.transcript ordinal message handle ∧
      (∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  exact of_counts setup checks wire route sign seed scalar pairs chosen challenge outer serverKeyId bounds mode work budget target
    bounded reserved chosenAt readback responseReadback before initialCounter initialMarker ownersEmpty keysEmpty initialPin candidate
    (RegistrationNativeSecretWordInstallLedger.prefix_counts setup checks wire route sign input inside provider outer
      target.2.val target.1.val publicPrekey candidate serverKeyId bounds before initialTrace)
    observed supported actualPath session handle designated accepted pinned

end BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleOrdinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleOrdinal.of_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleOrdinal.of_counts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleOrdinal.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleOrdinal.selected
