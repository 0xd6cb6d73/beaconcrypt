-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSelectedTests
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
/-! Original broadly designated peers have their exact protected descriptor at the same source installation ordinal under arbitrary persistent World interpretation. Original replies, every failed prefix and the full platform/private chronology are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Physical A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
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
noncomputable def unused : QueryImpl RegistrationNativeSecretWordService.Combined
    (OracleComp (PqxdhRecordLiftInterface.WorldSpec n))
  | .inl (.inl coin) => PqxdhRecordLiftInterface.coinLift coin
  | .inl (.inr _) => pure (List.Vector.replicate 76 0,List.Vector.replicate 32 0)
  | .inr _ => pure (List.Vector.replicate 76 0,List.Vector.replicate 32 0)

variable (candidate : MlKemSharedSecret)
variable (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "closedImpl" => RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate
  (unused (n := n)) (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge physical
abbrev NativePrivate (n : Nat) (KemSK : Type) := RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase
abbrev NativeResult (n : Nat) (KemSK Platform Physical A : Type) (source : RegistrationNativeMldsa.Source) :=
  ((((A × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) × RegistrationNativeG2Trace.State) × NativePrivate n KemSK) × Physical
abbrev SourceResult (n : Nat) (KemSK Platform Physical A : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeEvents.Observed A (RegistrationNativePlatformLorStatefulSupport.TracedState
    (RegistrationNativePlatformSecretWordOrdinary.State source Platform) (RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK × Physical))
noncomputable def sourceBefore (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical) :=
  ((RegistrationNativeG3NativeStartupFields.word before.1,before.2),
    (RegistrationNativeSecretWordFrontendTrace.initial,(RegistrationNativePlatformLorIdealInitial.symbolicPrivate privateBefore,physicalBefore)))
local notation "nativeHandler" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
  (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge candidate)

/-- Each supported actual closed native trace has the same complete symbolic source execution. -/
theorem source_result (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (result : NativeResult n KemSK Platform Physical A source)
    (supported : result ∈ support ((simulateQ physical ((simulateQ nativeHandler (RegistrationNativeG2Trace.program
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign
        target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)))).run privateBefore)).run physicalBefore)) :
    ∃ reached : SourceResult n KemSK Platform Physical A source,
      reached ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (RegistrationNativePlatformLorStatefulSupport.traced closedImpl controller) mode work (sourceBefore source before privateBefore physicalBefore)) ∧
      RegistrationNativePlatformLorIdealTraceRun.projectResult candidate reached=result := by
  have related := RegistrationNativePlatformLorIdealTraceRun.closed_source setup sign seed scalar candidate (unused (n := n))
    target.2.val pairs chosen.1 challenge checks target.2.val target.1.val publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer physical serverKeyId bounds mode work
    (RegistrationNativeG3NativeStartupFields.word before.1,before.2)
    (RegistrationNativePlatformLorIdealInitial.symbolicPrivate privateBefore) physicalBefore
  rw [RegistrationNativePlatformLorIdealInitial.frame_private candidate privateBefore pool phase] at related
  simp only [RegistrationNativePlatformSecretWordOrdinary.evaluate,Prod.map_apply,RegistrationNativeG3NativeStartupFields.word_eval,id_eq,Prod.mk.eta] at related
  rw [←related,support_map] at supported
  exact supported


/-- Original broad LR goodness selects every actual tested installation on this same ideal-service execution. -/
theorem lower_selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (serverPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (result : NativeResult n KemSK Platform Physical A source)
    (supported : result ∈ support ((simulateQ physical ((simulateQ nativeHandler (RegistrationNativeG2Trace.program
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign
        target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)))).run privateBefore)).run physicalBefore))
    (filter : RegistrationNativeLorEvents.Filter A)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target
      (result.1.1.1.1.1,result.1.1.1.1.2)) :
    RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto wire serverKeyId result.1.1.1.1.2 result.1.1.2.events
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  obtain ⟨reached,called,equal⟩ := source_result setup checks source sign seed scalar pairs chosen challenge view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target candidate physical
    before privateBefore physicalBefore pool phase result supported
  cases equal
  have contract := RegistrationNativePlatformLorCtxClosed.contract setup wire sign seed scalar candidate (unused (n := n)) target.2.val pairs chosen.1 challenge physical
  have selected := RegistrationNativePlatformLorSourceSelectedTests.all_tests setup checks source sign seed scalar pairs chosen challenge closedImpl (fun current => current.1.1.kem)
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target contract
    bounded reserved chosenAt (sourceBefore source before privateBefore physicalBefore) initialCounter rfl ownersEmpty rfl candidate rfl serverPin reached called filter good
  exact selected

/-- Original broad APP goodness selects its own claimed fresh installation even when no test was requested. -/
theorem lower_claimed (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (serverPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (result : NativeResult n KemSK Platform Physical A source)
    (supported : result ∈ support ((simulateQ physical ((simulateQ nativeHandler (RegistrationNativeG2Trace.program
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign
        target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)))).run privateBefore)).run physicalBefore))
    (claim : A → Option (Nat × Pqxdh.Bytes))
    (good : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim
      (result.1.1.1.1.1,(result.1.1.1.1.2,()))) :
    RegistrationNativeInstallTarget.Claimed claim result.1.1.1.1.1 result.1.1.1.1.2 result.1.1.2.events
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  obtain ⟨reached,called,equal⟩ := source_result setup checks source sign seed scalar pairs chosen challenge view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target candidate physical
    before privateBefore physicalBefore pool phase result supported
  cases equal
  have contract := RegistrationNativePlatformLorCtxClosed.contract setup wire sign seed scalar candidate (unused (n := n)) target.2.val pairs chosen.1 challenge physical
  have selected := RegistrationNativePlatformLorSourceSelectedTests.claimed setup checks source sign seed scalar pairs chosen challenge closedImpl (fun current => current.1.1.kem)
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target contract
    bounded reserved chosenAt (sourceBefore source before privateBefore physicalBefore) initialCounter rfl ownersEmpty rfl candidate rfl serverPin reached called claim good
  exact selected

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.source_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.source_result

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.lower_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.lower_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.lower_claimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.lower_claimed
