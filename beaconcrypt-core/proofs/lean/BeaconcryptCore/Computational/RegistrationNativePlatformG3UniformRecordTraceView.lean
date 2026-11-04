-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTrace
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
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
open RegistrationNativePlatformG3UniformRecordTrace (staged)
variable (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
local notation "cap" => budget.cap 4 + budget.cap 5
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)

noncomputable def run (modes : PqxdhRecordLiftWorldCompiler.Label (budget.cap 4+budget.cap 5) → PqxdhRecordLiftIdeal.KeyMode) :=
  (fun observed => (observed.1,RegistrationNativeRecordPackage.nativeView (observed.2.1.1.1,observed.2.1.2) observed.2.2.base.produced)) <$>
    staged setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous
      (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec) PqxdhRecordLiftIdeal.CtxPrivate.initial

/-- The same whole sampler and actual source trace erase to the literal complete record view. -/
theorem ctx_erase (modes : PqxdhRecordLiftWorldCompiler.Label (budget.cap 4+budget.cap 5) → PqxdhRecordLiftIdeal.KeyMode) :
    (fun observed => RegistrationNativePlatformSelectiveRecordTraceView.erase observed.2) <$>
      run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous modes =
    RegistrationNativeRecordPackage.ctx modes setup codec route
      (program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds .P adversary budget selected previous) := by
  rw [RegistrationNativeRecordPackage.ctx_source]
  have sourceLaw := congrArg (Functor.map (fun result : ((RegistrationNativeEntropyRun.Outcome
      (RegistrationNativePlatformSelectiveEntropyEnvironment.State cap KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control cap) × PqxdhRecordLiftIdeal.CtxPrivate cap =>
        RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) result.2.base.produced))
    (RegistrationNativePlatformG3UniformRecordTrace.interpret_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous
      (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec) PqxdhRecordLiftIdeal.CtxPrivate.initial)
  simpa only [run,Functor.map_map,RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativeRecordPackage.nativeView] using sourceLaw

/-- The actual same-sample view carries the source-derived selected hidden-slot receipt. -/
theorem hidden (modes : PqxdhRecordLiftWorldCompiler.Label (budget.cap 4+budget.cap 5) → PqxdhRecordLiftIdeal.KeyMode)
    (parameters : Sample KemSK (budget.cap 4+budget.cap 5))
    (observed : RegistrationNativeRecordPackage.View (budget.cap 4+budget.cap 5)
      (RegistrationNativePlatformSelectiveRecordTraceStartup.Extra (budget.cap 4+budget.cap 5) KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value)
    (supported : (parameters,observed) ∈ support (run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous modes)) :
    RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup parameters.seed parameters.scalar parameters.candidate observed := by
  rw [run,support_map] at supported
  obtain ⟨raw,rawSupport,same⟩ := supported
  cases same
  exact RegistrationNativePlatformG3UniformRecordTrace.hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous
    (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec) PqxdhRecordLiftIdeal.CtxPrivate.initial raw.1 raw.2 rawSupport raw.2.2.base.produced

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView.ctx_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView.ctx_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView.hidden
