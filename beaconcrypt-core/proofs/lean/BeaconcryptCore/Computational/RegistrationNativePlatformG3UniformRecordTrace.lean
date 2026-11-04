-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixState
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties
/-! The warm source trace retains each sampler result beside its actual reached record state. Chronology erasure and physical hidden-slot storage are derived on that same continuation, with private sampling costs retained. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTrace
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value Secret : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample program)
variable (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
local notation "cap" => budget.cap 4 + budget.cap 5
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)

noncomputable def after (parameters : Sample KemSK (budget.cap 4+budget.cap 5)) :=
  RegistrationNativePlatformSelectiveRecordTraceState.program (source := source) setup checks wire parameters.seed parameters.scalar parameters.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.materials) ensureInit identityIndex serverKeyId bounds .P adversary

noncomputable def staged (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec (budget.cap 4+budget.cap 5)) (StateT Secret ProbComp))
    (initialSecret : Secret) := do
  let sampled ← (simulateQ (RegistrationNativePlatformRecordPrefixState.coins service) (sample setup budget selected)).run initialSecret
  let result ← CborRawRecordOriginFlatten.interpret service codec route
    (after setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous sampled.1)
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl sampled.2
  pure (sampled.1,result)

/-- Chronology erasure recovers the complete literal whole-prefix client and its actual private coin state. -/
theorem interpret_source (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec (budget.cap 4+budget.cap 5)) (StateT Secret ProbComp))
    (initialSecret : Secret) :
    (fun observed => (((RegistrationNativePlatformSelectiveRecordTraceStartup.forget observed.2.1.1.1,observed.2.1.1.2),observed.2.1.2),observed.2.2)) <$>
      staged setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous service initialSecret =
    CborRawRecordOriginFlatten.interpret service codec route
      (program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds .P adversary budget selected previous)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret := by
  rw [program,CborRawRecordOriginFlatten.interpret_bind,RegistrationNativePlatformRecordPrefixState.sample,bind_map_left]
  simp only [staged,map_bind,bind_pure_comp,Functor.map_map]
  apply bind_congr
  intro sampled
  simpa only [after,RegistrationNativePlatformG3UniformRecordProgram.after] using
    (RegistrationNativePlatformSelectiveRecordTraceStateProperties.interpret_erase (source := source) setup checks wire sampled.1.seed sampled.1.scalar sampled.1.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val sampled.1.profile.pairs sampled.1.profile.publicKey sampled.1.profile.challenge sampled.1.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget sampled.1.materials) ensureInit identityIndex serverKeyId bounds .P adversary route service codec sampled.2)

/-- Every sampled source continuation has the hidden-slot receipt at its own reached private state. -/
theorem hidden (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec (budget.cap 4+budget.cap 5)) (StateT Secret ProbComp))
    (initialSecret : Secret) (parameters : Sample KemSK (budget.cap 4+budget.cap 5))
    (result : RegistrationNativePlatformSelectiveRecordTraceHidden.Result (budget.cap 4+budget.cap 5) KemSK
      RegistrationNativeKemSwitchSource.Phase Platform Secret Value source)
    (supported : (parameters,result) ∈ support (staged setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous service initialSecret))
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) :
    RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup parameters.seed parameters.scalar parameters.candidate
      (RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) produced) := by
  simp only [staged,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨sampled,_sampleSupport,result,resultSupport,same⟩ := supported
  cases same
  exact RegistrationNativePlatformSelectiveRecordTraceStateProperties.hidden setup checks wire sampled.1.seed sampled.1.scalar sampled.1.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val sampled.1.profile.pairs sampled.1.profile.publicKey sampled.1.profile.challenge sampled.1.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget sampled.1.materials) ensureInit identityIndex serverKeyId bounds .P adversary route service codec sampled.2 result resultSupport produced

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTrace.interpret_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTrace.interpret_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTrace.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTrace.hidden
