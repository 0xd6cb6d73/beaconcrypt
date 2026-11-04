-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDesignatedHandleOrdinal
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal
import BeaconcryptCore.Computational.RegistrationNativeDesignatedPeerTraced
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger
/-! Broad original native LR eligibility, with its real-origin-complement public pin conjunct, gives same-run selected installation receipts for every admitted test. No physical hiddenness is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests
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

def TestsSelected (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (ledger : RegistrationNativeLedger.State) (events : List RegistrationNativeG2Trace.Event)
    (selected : RegistrationNativeRelatedFamily.Message → Prop) : Prop :=
  RegistrationNativeLorCanonical.OnTests crypto wire serverKeyId ledger.ledger.transcript fun handle =>
    ∃ role ordinal message, RegistrationNativeInstallOrdinals.At role events ledger.transcript ordinal message handle ∧ selected message

/-- Every admitted test in the original good canonical LR event has its own protected installation receipt in the same final trace. -/
theorem all_tests (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (before : State n KemSK source) (initialCounter : before.1.1.parsedAccepts = 0)
    (initialMarker : before.2.kem.2 = none) (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (initialPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (candidate : MlKemSharedSecret) (initialTrace : before.1.2.events = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before))
    (actualPath : Path fullImpl (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (filter : RegistrationNativeLorEvents.Filter Value)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (observed.1, observed.2.1)) :
    TestsSelected setup.source.crypto wire serverKeyId observed.2.1
      (observed.2.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (fun message => ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typedImpl mode work before observed supported
  obtain ⟨session, eligible, accepted⟩ := RegistrationNativeLorCanonical.accepted setup.source.crypto wire serverKeyId budget filter target
    (observed.1, observed.2.1) consistent good.1
  intro pre entry post handle left right split query admitted
  have designated := eligible.2.2 pre entry post handle left right split query admitted
  have pinned := good.2 pre entry post handle left right split query admitted
  exact RegistrationNativeDesignatedHandleOrdinal.selected setup checks wire route sign seed scalar pairs chosen challenge outer
    serverKeyId bounds mode work budget target bounded reserved chosenAt readback responseReadback before initialCounter initialMarker ownersEmpty keysEmpty
    initialPin candidate initialTrace observed supported actualPath session handle designated accepted pinned

/-- The complete actual alias result retains every admitted test's selected installation receipt. -/
theorem alias_selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (before : RegistrationNativeSecretWordMessage.State source) (initialCounter : before.parsedAccepts = 0)
    (ownersEmpty : before.beacons = [])
    (initialPin : PqxdhRefinement.absBytes before.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (candidate : MlKemSharedSecret)
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)
    (supported : result ∈ support (simulateQ outer (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign input inside provider
      target.2.val target.1.val publicPrekey serverKeyId bounds mode work before ordinary (RegistrationNativeSecretWordKemPool.empty, none))))
    (filter : RegistrationNativeLorEvents.Filter Value)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (result.1.1.1.1, result.1.1.1.2)) :
    TestsSelected setup.source.crypto wire serverKeyId result.1.1.1.2
      (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (fun message => ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  have actual := Set.mem_image_of_mem RegistrationNativeSecretWordTargetAliasOrdinal.observed supported
  rw [← support_map, RegistrationNativeSecretWordTargetAliasOrdinal.closed_source setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds mode work before ordinary (RegistrationNativeSecretWordKemPool.empty, none)] at actual
  have path := (RegistrationNativeSecretWordTargetTracedPath.run setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds mode work
    ((before, RegistrationNativeSecretWordFrontendTrace.initial), RegistrationNativeSecretWordInterpreter.initial ordinary
      (RegistrationNativeSecretWordKemPool.empty, none)) (RegistrationNativeSecretWordTargetAliasOrdinal.observed result) actual).1
  exact all_tests setup checks wire route sign seed scalar pairs chosen challenge outer serverKeyId bounds mode work budget target
    bounded reserved chosenAt readback responseReadback
    ((before, RegistrationNativeSecretWordFrontendTrace.initial), RegistrationNativeSecretWordInterpreter.initial ordinary
      (RegistrationNativeSecretWordKemPool.empty, none)) initialCounter rfl ownersEmpty rfl initialPin candidate rfl
    (RegistrationNativeSecretWordTargetAliasOrdinal.observed result) actual path filter good

end BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests.all_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests.all_tests
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests.alias_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests.alias_selected
