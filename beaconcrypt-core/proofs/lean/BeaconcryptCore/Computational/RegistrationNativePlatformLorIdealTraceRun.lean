-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix
/-! Concrete source leaf instantiation for the actual post-agreement Beacon suffix. Material addresses are evaluated before the same selective demand; hidden, known and refused choices and every stateful World continuation remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World)
open RegistrationNativePlatformLorIdealTraceRealization (Symbolic)
local notation "frame" => RegistrationNativePlatformLorIdealTraceLeaves.project
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
variable (setup : Setup base KemSK)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolic" => RegistrationNativePlatformLorIdealTraceLeaves.symbolicTrace setup wire sign seed scalar candidate unused selected pairs publicKey challenge
local notation "actual" => RegistrationNativePlatformLorIdealTraceLeaves.nativeTrace setup wire sign seed scalar candidate selected pairs publicKey challenge
local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "nativeLocal" => wordLocal ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate
local notation "actualLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false

local notation "reified" => RegistrationNativePlatformLorIdealTraceRealization.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge

variable {Platform E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : PqxdhServerAuthExperiment.Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "evaluate" => RegistrationNativePlatformSecretWordOrdinary.evaluate candidate
local notation "nativeController" => RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "wordController" => RegistrationNativePlatformSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

local notation "nativeTyped" => RegistrationNativePlatformLorIdealTraceFrontend.nativeTyped setup wire sign seed scalar candidate selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "nativeHandler" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
  (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate)

omit primitive in
private theorem trace_initial : RegistrationNativeSecretWordCheckedTrace.state candidate RegistrationNativeSecretWordFrontendTrace.initial=RegistrationNativeG2Trace.initial := rfl

theorem native_source {A : Type} (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase) :
    (fun result => (((result.1,result.2.1),result.2.2.1),result.2.2.2)) <$>
      (simulateQ nativeTyped (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run
        (before,(RegistrationNativeG2Trace.initial,privateBefore)) =
      (simulateQ nativeHandler (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)))).run privateBefore := by
  unfold RegistrationNativePlatformLorIdealTraceFrontend.nativeTyped
  rw [RegistrationNativePlatformLorStagedProgram.controller_program]
  simp only [QueryImpl.simulateQ_compose]
  rw [RegistrationNativePlatformLorIdealTraceLeaves.nativeTrace,RegistrationNativePlatformLorStagedProgram.trace_program]
  simp only [Functor.map_map,RegistrationNativeG2Trace.program,RegistrationNativePlatformPublicFrontend.run]
  simp only [Prod.mk.eta,id_map']

def projectResult {A Physical : Type} (result : A × (RegistrationNativeLedger.State ×
    (RegistrationNativePlatformSecretWordOrdinary.State source Platform ×
      (RegistrationNativeSecretWordFrontendTrace.State × (RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK × Physical))))) :=
  (((((result.1,result.2.1),evaluate result.2.2.1),RegistrationNativeSecretWordCheckedTrace.state candidate result.2.2.2.1),
    RegistrationNativePlatformLorCtxLeaves.frame candidate result.2.2.2.2.1),result.2.2.2.2.2)

variable {Physical : Type} (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
theorem closed_source {A : Type} (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK)
    (physicalBefore : Physical) :
    projectResult candidate <$>
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (RegistrationNativePlatformLorStatefulSupport.traced
          (RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical) wordController)
        mode work (before,(RegistrationNativeSecretWordFrontendTrace.initial,(privateBefore,physicalBefore))) =
      (simulateQ physical ((simulateQ nativeHandler (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work (evaluate before))))).run
          (RegistrationNativePlatformLorCtxLeaves.frame candidate privateBefore))).run physicalBefore := by
  have related := RegistrationNativePlatformLorIdealTraceFrontend.full_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work
    (before,(RegistrationNativeSecretWordFrontendTrace.initial,privateBefore))
  have mapped := congrArg (Functor.map (fun result => (((result.1,result.2.1),result.2.2.1),result.2.2.2))) related
  simp only [RegistrationNativePlatformLorIdealTraceFrontend.projectState,RegistrationNativePlatformLorIdealTraceLeaves.project,
    Prod.map_apply,trace_initial] at mapped
  rw [native_source setup sign seed scalar candidate selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work] at mapped
  have physicalEq := congrArg (fun tree => (simulateQ physical tree).run physicalBefore) mapped
  have folded := RegistrationNativePlatformLorPhysicalClosing.full
    (RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)) physical wordController setup.source.crypto wire serverKeyId bounds mode work
    before RegistrationNativeSecretWordFrontendTrace.initial privateBefore physicalBefore
  have fullMapped := congrArg (Functor.map (fun result : (A × (RegistrationNativeLedger.State ×
      (RegistrationNativePlatformSecretWordOrdinary.State source Platform × (RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK)))) × Physical =>
        (((((result.1.1,result.1.2.1),evaluate result.1.2.2.1),RegistrationNativeSecretWordCheckedTrace.state candidate result.1.2.2.2.1),
          RegistrationNativePlatformLorCtxLeaves.frame candidate result.1.2.2.2.2),result.2))) folded
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,RegistrationNativePlatformLorIdealTraceFrontend.wordTyped,
    RegistrationNativePlatformLorPhysicalClosing.typed,RegistrationNativePlatformLorPhysicalClosing.trace,
    RegistrationNativePlatformLorIdealTraceLeaves.symbolicTrace] at fullMapped physicalEq
  exact fullMapped.trans physicalEq

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun.native_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun.closed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun.closed_source
