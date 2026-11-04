-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelectedStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView
import BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordObserver
import BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryObserverSecurity
import BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage
/-! Same-result descriptor receipts attach original warm source observers to their native physical ideal baselines. Genuine reserved sampling and startup internally supply the source designation receipt; no runtime identity or real-to-ideal support inclusion is used. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample)
variable (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (target : Fin budget.accept × Fin budget.capacity) (previous : Platform)
local notation "chosenIndex" => Prod.snd target
local notation "selectedAccept" => Fin.val (Prod.fst target)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "reserveFrame" => reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "cap" => budget.cap 4+budget.cap 5
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "traced" => RegistrationNativePlatformG3UniformRecordTraceView.run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget chosenIndex previous (fun _ => PqxdhRecordLiftIdeal.KeyMode.random)
local notation "TraceView" => RegistrationNativeRecordPackage.View cap (RegistrationNativePlatformSelectiveRecordTraceStartup.Extra cap KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value
local notation "codec" => RegistrationNativeWire.ledgerCodec canonical
local notation "service" => PqxdhRecordLiftIdeal.ctxInterpreter (n := cap) (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) id setup codec

include bounded in
/-- The genuine complete warm sampler and startup derive the original same-result descriptor receipt internally. -/
theorem selected (filter : RegistrationNativeLorEvents.Filter Value) :
    ∀ (parameters : Sample KemSK (budget.cap 4+budget.cap 5)) (observed : TraceView),
      (parameters,observed) ∈ support traced →
      ∀ finished ∈ observed.result,
        RegistrationNativeLorCanonical.GoodAt setup.source.crypto canonical serverKeyId budget filter target finished.2.1 →
        RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto canonical serverKeyId finished.2.1.2 finished.2.2.2.events
          (RegistrationNativePlatformInstallKernelStorage.Selected setup parameters.seed parameters.scalar parameters.candidate) := by
  intro parameters observed supported finished present good
  rw [RegistrationNativePlatformG3UniformRecordTraceView.run,support_map] at supported
  obtain ⟨raw,called,equal⟩ := supported
  cases equal
  obtain ⟨reserved,chosen,chosenAt,chosenPublic⟩ := RegistrationNativePlatformG3UniformRecordSample.staged_selected
    setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds adversary budget chosenIndex previous service PqxdhRecordLiftIdeal.CtxPrivate.initial raw.1 raw.2 called
  simp only [RegistrationNativePlatformG3UniformRecordTrace.staged,mem_support_bind_iff,mem_support_pure_iff] at called
  obtain ⟨sampled,_sampleSupport,actual,resultSupport,same⟩ := called
  cases same
  have genuine : sampled.1.profile.pairs[(Fin.val (Prod.snd target))]?=some (sampled.1.profile.publicKey,chosen.2) :=
    chosenAt.trans (congrArg some (Prod.ext chosenPublic rfl))
  exact RegistrationNativePlatformLorIdealSelected.ctx_selected setup checks source sampled.1.seed sampled.1.scalar sampled.1.profile.pairs
    (sampled.1.profile.publicKey,chosen.2) sampled.1.profile.challenge view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reservePackets serverKeyId bounds .P adversary budget target sampled.1.candidate previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget sampled.1.materials) ensureInit identityIndex service codec route
    bounded reserved genuine rfl rfl sampled.2 actual resultSupport finished present filter good

include bounded in
/-- The genuine complete warm sampler and startup derive the original same-result descriptor receipt internally. -/
theorem claimed (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    ∀ (parameters : Sample KemSK (budget.cap 4+budget.cap 5)) (observed : TraceView),
      (parameters,observed) ∈ support traced →
      ∀ finished ∈ observed.result,
        RegistrationNativePrekeyEvents.GoodAt setup.source.crypto canonical serverKeyId budget target claim (finished.2.1.1,(finished.2.1.2,())) →
        RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events
          (RegistrationNativePlatformInstallKernelStorage.Selected setup parameters.seed parameters.scalar parameters.candidate) := by
  intro parameters observed supported finished present good
  rw [RegistrationNativePlatformG3UniformRecordTraceView.run,support_map] at supported
  obtain ⟨raw,called,equal⟩ := supported
  cases equal
  obtain ⟨reserved,chosen,chosenAt,chosenPublic⟩ := RegistrationNativePlatformG3UniformRecordSample.staged_selected
    setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds adversary budget chosenIndex previous service PqxdhRecordLiftIdeal.CtxPrivate.initial raw.1 raw.2 called
  simp only [RegistrationNativePlatformG3UniformRecordTrace.staged,mem_support_bind_iff,mem_support_pure_iff] at called
  obtain ⟨sampled,_sampleSupport,actual,resultSupport,same⟩ := called
  cases same
  have genuine : sampled.1.profile.pairs[(Fin.val (Prod.snd target))]?=some (sampled.1.profile.publicKey,chosen.2) :=
    chosenAt.trans (congrArg some (Prod.ext chosenPublic rfl))
  exact RegistrationNativePlatformLorIdealSelected.ctx_claimed setup checks source sampled.1.seed sampled.1.scalar sampled.1.profile.pairs
    (sampled.1.profile.publicKey,chosen.2) sampled.1.profile.challenge view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reservePackets serverKeyId bounds .P adversary budget target sampled.1.candidate previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget sampled.1.materials) ensureInit identityIndex service codec route
    bounded reserved genuine rfl rfl sampled.2 actual resultSupport finished present claim good

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected.claimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected.claimed
