-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealCborSelected
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Secret Reader Response A : Type} {base : OracleSpec I}
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
variable (candidate : MlKemSharedSecret)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route
local notation "nativeHandler" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
  (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge candidate)
abbrev StageResult (n : Nat) (KemSK Platform A : Type) (source : RegistrationNativeMldsa.Source) :=
  (((A × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) × RegistrationNativeG2Trace.State) ×
    RegistrationNativePlatformLorIdealSelected.NativePrivate n KemSK
abbrev Result (n : Nat) (KemSK Platform Secret A : Type) (source : RegistrationNativeMldsa.Source) :=
  ((StageResult n KemSK Platform A source × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret

theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (serverPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (privateBefore : RegistrationNativePlatformLorIdealSelected.NativePrivate n KemSK)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n KemSK Platform Secret A source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ nativeHandler (RegistrationNativeG2Trace.program
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign
          target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)))).run privateBefore)
      shell control secret))
    (filter : RegistrationNativeLorEvents.Filter A)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target
      (result.1.1.1.1.1.1.1,result.1.1.1.1.1.1.2)) :
    RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto wire serverKeyId result.1.1.1.1.1.1.2 result.1.1.1.1.2.events
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  have actual := Set.mem_image_of_mem (fun returned : Result n KemSK Platform Secret A source =>
    (returned.1.1.1,(returned.1.1.2,(returned.1.2,returned.2)))) supported
  rw [←support_map,←RegistrationNativePlatformLorIdealPhysical.program_source service codec route _ (shell,(control,secret))] at actual
  exact RegistrationNativePlatformLorIdealSelected.lower_selected setup checks source sign seed scalar pairs chosen challenge view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    serverKeyId bounds mode work budget target candidate physical bounded reserved chosenAt before initialCounter ownersEmpty serverPin privateBefore
    (shell,(control,secret)) pool phase (result.1.1.1,(result.1.1.2,(result.1.2,result.2))) actual filter good

theorem claimed (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (serverPin : PqxdhRefinement.absBytes before.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (privateBefore : RegistrationNativePlatformLorIdealSelected.NativePrivate n KemSK)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n KemSK Platform Secret A source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ nativeHandler (RegistrationNativeG2Trace.program
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign
          target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)))).run privateBefore)
      shell control secret))
    (claim : A → Option (Nat × Pqxdh.Bytes))
    (good : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim
      (result.1.1.1.1.1.1.1,(result.1.1.1.1.1.1.2,()))) :
    RegistrationNativeInstallTarget.Claimed claim result.1.1.1.1.1.1.1 result.1.1.1.1.1.1.2 result.1.1.1.1.2.events
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  have actual := Set.mem_image_of_mem (fun returned : Result n KemSK Platform Secret A source =>
    (returned.1.1.1,(returned.1.1.2,(returned.1.2,returned.2)))) supported
  rw [←support_map,←RegistrationNativePlatformLorIdealPhysical.program_source service codec route _ (shell,(control,secret))] at actual
  exact RegistrationNativePlatformLorIdealSelected.lower_claimed setup checks source sign seed scalar pairs chosen challenge view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    serverKeyId bounds mode work budget target candidate physical bounded reserved chosenAt before initialCounter ownersEmpty serverPin privateBefore
    (shell,(control,secret)) pool phase (result.1.1.1,(result.1.1.2,(result.1.2,result.2))) actual claim good
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealCborSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealCborSelected.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealCborSelected.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealCborSelected.claimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealCborSelected.claimed
