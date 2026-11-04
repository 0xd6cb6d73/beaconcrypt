import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerOrdinal
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedPeerOrdinal
import BeaconcryptCore.Computational.RegistrationNativeLorSelectedTests
import BeaconcryptCore.Computational.RegistrationNativeInstallTarget
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPin
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath
import BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetDesignatedRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
import BeaconcryptCore.Computational.RegistrationNativeLinkedBuild
/-! Original broad peer designation and its transported public pin conjunct identify the exact protected Ready at the actual later successful moved-token build. The proof uses the current stateful source writer and retains one original run, all failed prefixes, complete platform/private state and its full suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
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
variable (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem
  (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.traced implementation controller
local notation "State" => RegistrationNativePlatformLorStatefulSupport.TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State
include contract

theorem selected_handle (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2.2).2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2.2).1.keys=[])
    (candidate : MlKemSharedSecret) (initialTrace : before.2.1.events=[])
    (serverPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Fin budget.accept) (handle : PqxdhDeploymentInterface.Handle)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript handle=some (session,target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId observed.2.1.ledger.transcript handle) :
    ∃ role ordinal message,RegistrationNativeInstallOrdinals.At role
      (observed.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) observed.2.1.transcript ordinal message handle ∧
      RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate message := by
  cases handle with
  | peer keyId =>
    obtain ⟨ordinal,message,paired,selected⟩ := RegistrationNativePlatformLorSourceDesignatedPeerOrdinal.ordinal setup checks source sign seed scalar pairs chosen challenge
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target
      implementation kem contract bounded reserved chosenAt before initialCounter initialMarker ownersEmpty keysEmpty candidate initialTrace observed supported session keyId designated accepted pinned
    exact ⟨.server,ordinal,message,paired,selected⟩
  | owner index =>
    obtain ⟨ordinal,message,paired,selected⟩ := RegistrationNativePlatformLorSourceOwnerOrdinal.ordinal setup checks source sign seed scalar pairs chosen challenge implementation kem
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target contract
      bounded reserved chosenAt before initialCounter initialMarker ownersEmpty keysEmpty candidate initialTrace serverPin observed supported session index designated accepted
    exact ⟨.beacon,ordinal,message,paired,selected⟩

theorem all_tests (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2.2).2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2.2).1.keys=[])
    (candidate : MlKemSharedSecret) (initialTrace : before.2.1.events=[])
    (serverPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (filter : RegistrationNativeLorEvents.Filter A)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (observed.1,observed.2.1)) :
    RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto wire serverKeyId observed.2.1
      (observed.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  obtain ⟨session,eligible,accepted⟩ := RegistrationNativeLorCanonical.accepted setup.source.crypto wire serverKeyId budget filter target
    (observed.1,observed.2.1) consistent good.1
  intro pre entry post handle left right split query admitted
  exact selected_handle setup checks source sign seed scalar pairs chosen challenge implementation kem view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    serverKeyId bounds mode work budget target contract bounded reserved chosenAt before initialCounter initialMarker ownersEmpty keysEmpty candidate initialTrace serverPin observed supported session handle
    (eligible.2.2 pre entry post handle left right split query admitted) accepted (good.2 pre entry post handle left right split query admitted)

theorem claimed (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2.2).2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2.2).1.keys=[])
    (candidate : MlKemSharedSecret) (initialTrace : before.2.1.events=[])
    (serverPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (claim : A → Option (Nat × Pqxdh.Bytes))
    (good : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim observed) :
    RegistrationNativeInstallTarget.Claimed claim observed.1 observed.2.1
      (observed.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  obtain ⟨index,guess,entry,session,claimed,fresh,designated,accepted,guessed,pinned⟩ := good
  obtain ⟨role,ordinal,message,paired,selected⟩ := selected_handle setup checks source sign seed scalar pairs chosen challenge implementation kem view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    serverKeyId bounds mode work budget target contract bounded reserved chosenAt before initialCounter initialMarker ownersEmpty keysEmpty candidate initialTrace serverPin observed supported session entry.handle designated accepted pinned
  exact ⟨index,guess,entry,role,ordinal,message,claimed,fresh,guessed,paired,selected⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests.selected_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests.selected_handle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests.all_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests.all_tests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests.claimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests.claimed
