import BeaconcryptCore.Computational.RegistrationNativePlatformLorSelectedTests
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable
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

/-! The actual corrected full source, complete alias client and byte realization retain arbitrary same-result observation when original broad LR eligibility is replaced by its derived selected-install receipt. This is an operational event implication on the same ledger and source/platform/private result; no random-provider or ideal-game identification is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource
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

local notation "actualClient" => RegistrationNativePlatformSecretWordAliasClient.client setup checks RegistrationNativePlatformConcreteSource.wire source sign
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route nativeInput nativeInside provider
  serverKeyId bounds mode work
/-- An arbitrary observer of the literal full result survives the original good-event to selected-install implication. -/
theorem full_probability (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : before.2.2.kem.2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : before.2.2.kem.1.keys=[])
    (candidate : MlKemSharedSecret) (initialTrace : before.2.1.events=[])
    (serverPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (filter : RegistrationNativeLorEvents.Filter A) (observe : RegistrationNativeEvents.Observed A State → Bool) :
    Pr{let result ← RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before}[
      RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (result.1,result.2.1) ∧ observe result=true] ≤
    Pr{let result ← RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before}[
      TestsSelected setup.source.crypto wire serverKeyId result.2.1
        (result.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
        (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) ∧ observe result=true] := by
  classical
  apply prEvent_mono_of_support
  intro result supported winning
  exact ⟨RegistrationNativePlatformLorSelectedTests.all_tests setup checks source route sign seed scalar pairs chosen challenge outer view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target bounded reserved chosenAt before initialCounter
    initialMarker ownersEmpty keysEmpty candidate initialTrace serverPin result supported filter winning.1,winning.2⟩

/-- Any observer of the complete same alias result is retained when original broad LR eligibility is replaced by its derived selected-install receipt. -/
theorem alias_probability (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (serverPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (candidate : MlKemSharedSecret)
    (filter : RegistrationNativeLorEvents.Filter A)
    (observe : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform → Bool) :
    Pr{let result ← simulateQ outer (actualClient before ordinary (RegistrationNativeSecretWordKemPool.empty,none))}[
      RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (result.1.1.1.1,result.1.1.1.2) ∧ observe result=true] ≤
    Pr{let result ← simulateQ outer (actualClient before ordinary (RegistrationNativeSecretWordKemPool.empty,none))}[
      TestsSelected setup.source.crypto wire serverKeyId result.1.1.1.2
        (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
        (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) ∧ observe result=true] := by
  classical
  apply prEvent_mono_of_support
  intro result supported winning
  exact ⟨RegistrationNativePlatformLorSelectedTests.alias_selected setup checks source route sign seed scalar pairs chosen challenge outer view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target bounded reserved chosenAt before initialCounter ownersEmpty
    serverPin ordinary candidate result supported filter winning.1,winning.2⟩

/-- The actual candidate-independent byte client retains that same observer after its genuine independent finite-table realization; no fixed/uniform provider identity is assumed. -/
theorem bytes_probability (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (serverPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (candidate : MlKemSharedSecret)
    (filter : RegistrationNativeLorEvents.Filter A)
    (observe : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform → Bool) :
    Pr{let result ← (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
      (actualClient before ordinary (RegistrationNativeSecretWordKemPool.empty,none))).run' ∅}[
      RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target (result.1.1.1.1,result.1.1.1.2) ∧ observe result=true] ≤
    Pr{let result ← (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
      (actualClient before ordinary (RegistrationNativeSecretWordKemPool.empty,none))).run' ∅}[
      TestsSelected setup.source.crypto wire serverKeyId result.1.1.1.2
        (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
        (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) ∧ observe result=true] := by
  classical
  let actual := actualClient before ordinary (RegistrationNativeSecretWordKemPool.empty,none)
  let : MeasurableSpace (RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform) := ⊤
  let : DiscreteMeasurableSpace (RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform) := ⟨fun _ => trivial⟩
  have sourceEq := _root_.EvalDistEq.of_evalDist_eq (RegistrationNativeSecretWordAliasTable.bytes_eager setup.source candidate actual).evalDist_eq
  rw [sourceEq.prEvent_eq,sourceEq.prEvent_eq]
  apply prEvent_mono_of_support
  intro result supported winning
  rw [mem_support_bind_iff] at supported
  obtain ⟨table,_sampled,called⟩ := supported
  exact ⟨RegistrationNativePlatformLorSelectedTests.alias_selected setup checks source route sign seed scalar pairs chosen challenge
    (RegistrationNativeSecretWordAliasTable.normalizedFixed table setup.source candidate) view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    serverKeyId bounds mode work budget target bounded reserved chosenAt before initialCounter ownersEmpty serverPin ordinary candidate result called filter winning.1,winning.2⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource.full_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource.full_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource.alias_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource.alias_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource.bytes_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource.bytes_probability
