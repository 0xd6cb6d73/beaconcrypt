import BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerOrdinal
import BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedOwnerOrdinal
import BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAlias
import BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedOwnerInputs
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerTracedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallMonotone
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage

/-! Every original broadly eligible admitted test has a selected installation in its same actual new source execution. The proof uses the original final ledger and source trace, actual stateful registration writers and all supported failure histories; selected-install receipts are derived before any physical hidden-slot transfer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSelectedTests
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativePlatformSecretWordExecution (TracedState drop)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity)
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "nativeInside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "publicPrekey" => setup.dh.publicKey scalar
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "plainTyped" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign nativeInput nativeInside provider outer controller
local notation "typed" => RegistrationNativePlatformSecretWordExecution.traced (n := n) setup wire route sign nativeInput nativeInside provider outer controller
local notation "State" => TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordKemEarly.early


open RegistrationNativeLorSelectedTests (TestsSelected)
/-- The same original broad LR good event gives a protected same-run installation for every admitted test under the literal current source callbacks. -/
theorem all_tests (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : before.2.2.kem.2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : before.2.2.kem.1.keys=[])
    (candidate : MlKemSharedSecret) (initialTrace : before.2.1.events=[])
    (serverPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (filter : RegistrationNativeLorEvents.Filter A)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (observed.1,observed.2.1)) :
    TestsSelected setup.source.crypto wire serverKeyId observed.2.1
      (observed.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  obtain ⟨session,eligible,accepted⟩ := RegistrationNativeLorCanonical.accepted setup.source.crypto wire serverKeyId budget filter target
    (observed.1,observed.2.1) consistent good.1
  intro pre entry post handle left right split query admitted
  have designated := eligible.2.2 pre entry post handle left right split query admitted
  have pinned := good.2 pre entry post handle left right split query admitted
  cases handle with
  | peer keyId =>
    obtain ⟨ordinal,message,paired,selected⟩ := RegistrationNativePlatformDesignatedPeerOrdinal.ordinal setup checks source route sign seed scalar pairs chosen challenge outer
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target
      bounded reserved chosenAt before initialCounter initialMarker ownersEmpty keysEmpty candidate initialTrace observed supported session keyId designated accepted pinned
    exact ⟨.server,ordinal,message,paired,selected⟩
  | owner owner =>
    obtain ⟨ordinal,message,paired,selected⟩ := RegistrationNativePlatformDesignatedOwnerOrdinal.ordinal setup checks source route sign seed scalar pairs chosen challenge outer
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target
      bounded reserved chosenAt before initialCounter initialMarker ownersEmpty keysEmpty candidate initialTrace serverPin observed supported session owner designated accepted
    exact ⟨.beacon,ordinal,message,paired,selected⟩

/-- The complete current alias client retains every admitted test's selected receipt on the same original ledger and full source/platform result. -/
theorem alias_selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (serverPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (candidate : MlKemSharedSecret)
    (result : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform)
    (supported : result ∈ support (simulateQ outer (RegistrationNativePlatformSecretWordAliasClient.client setup checks RegistrationNativePlatformConcreteSource.wire source sign
      target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route nativeInput nativeInside provider
      serverKeyId bounds mode work before ordinary (RegistrationNativeSecretWordKemPool.empty,none))))
    (filter : RegistrationNativeLorEvents.Filter A)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (result.1.1.1.1,result.1.1.1.2)) :
    TestsSelected setup.source.crypto wire serverKeyId result.1.1.1.2
      (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  have actual := Set.mem_image_of_mem (RegistrationNativePlatformSecretWordTargetAlias.observed source) supported
  rw [←support_map,RegistrationNativePlatformSecretWordTargetAlias.closed_source setup checks RegistrationNativePlatformConcreteSource.wire source sign
    target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route nativeInput nativeInside provider
    serverKeyId bounds mode work before ordinary (RegistrationNativeSecretWordKemPool.empty,none) outer] at actual
  exact all_tests setup checks source route sign seed scalar pairs chosen challenge outer view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    serverKeyId bounds mode work budget target bounded reserved chosenAt
    (before,(RegistrationNativeSecretWordFrontendTrace.initial,RegistrationNativeSecretWordInterpreter.initial ordinary (RegistrationNativeSecretWordKemPool.empty,none)))
    initialCounter rfl ownersEmpty rfl candidate rfl serverPin
    (RegistrationNativePlatformSecretWordTargetAlias.observed source result) actual filter good
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSelectedTests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSelectedTests.all_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSelectedTests.all_tests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSelectedTests.alias_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSelectedTests.alias_selected
