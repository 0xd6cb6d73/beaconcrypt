-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordDesignatedHandle
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPinnedDescriptor
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
open RegistrationNativePlatformLorIdealSelected (unused NativePrivate NativeResult SourceResult sourceBefore)
variable (candidate : MlKemSharedSecret)
variable (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "closedImpl" => RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate
  (unused (n := n)) (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge physical
local notation "nativeHandler" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
  (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge candidate)

/-- The complete original public pin-filtered target event yields its SAME selected descriptor and successful install ordinal under the actual source/physical interpretation. Session and parsed selector remain distinct. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
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
    (route : RawCtxServerRouting.SenderDecoder) (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
    (publicEvent : RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto wire serverKeyId budget
      route kind target result.1.1.1.1) :
    ∃priorList entry later, ∃session : Fin budget.accept, ∃handle role ordinal message,
      result.1.1.1.1.2.ledger.transcript=priorList++entry::later ∧
      RegistrationNativePlatformRecordSessionTargets.Witness setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget route kind (session,target.2) result.1.1.1.1.2.ledger.transcript priorList entry ∧
      RegistrationNativePlatformRecordSessionTargets.claimedHandle route kind entry=some handle ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget result.1.1.1.1.2.ledger.transcript handle=some (session,target.2) ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.1.1.1.1.2.transcript session.val target.1.val ∧
      RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId result.1.1.1.1.2.ledger.transcript handle ∧
      RegistrationNativeInstallOrdinals.At role result.1.1.2.events result.1.1.1.1.2.transcript ordinal message handle ∧
      RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate message := by
  obtain ⟨priorList,entry,later,sessionTarget,actual,witness,owner,accepted,pinned⟩:=publicEvent
  obtain ⟨handle,claimed,designated⟩:=RegistrationNativePlatformRecordSessionTargets.witness_handle setup.source.crypto
    (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget route kind sessionTarget _ priorList entry witness
  have sameTarget : sessionTarget=(sessionTarget.1,target.2):=Prod.ext rfl owner
  have designated' : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget result.1.1.1.1.2.ledger.transcript handle=some (sessionTarget.1,target.2) := by
    rw [←sameTarget]
    exact designated
  have actualPin:=pinned handle claimed
  obtain ⟨role,ordinal,message,installed,chosenMessage⟩:=RegistrationNativePlatformRecordDesignatedHandle.lower_handle setup checks source sign seed scalar pairs chosen challenge
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target candidate physical
    bounded reserved chosenAt before initialCounter ownersEmpty serverPin privateBefore physicalBefore pool phase result supported sessionTarget.1 handle designated' accepted actualPin
  refine ⟨priorList,entry,later,sessionTarget.1,handle,role,ordinal,message,actual,?_,claimed,designated',accepted,actualPin,installed,chosenMessage⟩
  rw [←sameTarget]
  exact witness
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPinnedDescriptor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPinnedDescriptor.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPinnedDescriptor.selected
