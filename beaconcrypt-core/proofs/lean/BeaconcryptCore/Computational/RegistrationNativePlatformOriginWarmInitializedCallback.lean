-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedPendingBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmInitializedCallback
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativePlatformOriginJournalProgram (Front Calls Client)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value View : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (env : RegistrationNativeHiddenStartup.Started source → RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : RegistrationNativeHiddenStartup.Started source → Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (route : RawCtxServerRouting.SenderDecoder)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : RegistrationNativeHiddenStartup.Started source → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (initial : RegistrationNativeHiddenStartup.Started source → Platform)
    (observe : RegistrationNativeHiddenStartup.Started source → Front n Platform → View)
local notation "concrete" => RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
local notation "compile" => RegistrationNativePlatformOriginStartupTails.compile concrete route
local notation "world" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve concrete bounds mode work initial
local notation "front(" born ")" => RegistrationNativeObservedStageTrace.handler (observe born)
  (RegistrationNativePlatformOriginFreeFullTrace.frontend (RegistrationNativeEntropyPort.environment (env born))
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto concrete route serverKeyId bounds)
local notation "X" => (Client n Platform Value × Option (Option (RegistrationNativePlatformOriginCallbackFreeStop.PublicCall PqxdhDeploymentInterface.FullSpec) × Value)) × Calls View
local notation "S" => (Front n Platform × Calls View) × CtxPrivate n
local notation "counted" => RegistrationNativePlatformOriginSendCallbackBudget.Sending
local notation "compiled(" born ")" => RegistrationNativePlatformOriginSelectedProgram.compiled source mode work born
local notation "before(" born "," shell "," control "," privateBefore ")" =>
  (((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]),privateBefore)

local instance : MeasurableSpace ((Client n Platform Value × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((Client n Platform Value × CtxPrivate n) × Bool) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (RegistrationNativePlatformOriginCallbackTrace.Result PqxdhDeploymentInterface.FullSpec S Value) := ⊤
local instance : DiscreteMeasurableSpace (RegistrationNativePlatformOriginCallbackTrace.Result PqxdhDeploymentInterface.FullSpec S Value) := ⟨fun _=>trivial⟩

/-- The whole genuine initialized source averages all startup failures and all attempted callback ordinals, deriving both original resource allowances internally. The same original complete outcome and reached private state remain beside the flag. -/
theorem bound (start : CtxPrivate n) (virgin : PqxdhRecordFactsPrivateCacheSource.Virgin start [])
    (initialEmpty : ∀label,(start.keys label).1.successfulSeals=[]) (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes →Pqxdh.Bytes) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀born,RegistrationNativeInterface.Respects budget (work born)) :
    𝒟[RegistrationNativePlatformOriginInitializedCallback.program setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) (start)]
      {result|result.2=true}≤budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  let service:=PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete
  have raw:=RegistrationNativePlatformOriginRawBudget.raw setup source ensureInit identityIndex serverKeyId identity env reserve concrete bounds mode work initial route budget bounded
  unfold RegistrationNativePlatformOriginInitializedCallback.program
  let : MeasurableSpace (((Option (RegistrationNativeHiddenStartup.Started source) × CborRecordWorldClient.Shell) × Control n) × CtxPrivate n) := ⊤
  let : DiscreteMeasurableSpace (((Option (RegistrationNativeHiddenStartup.Started source) × CborRecordWorldClient.Shell) × Control n) × CtxPrivate n) := ⟨fun _=>trivial⟩
  apply PqxdhRecordFactsOriginAverage.bind_le
  intro started supported
  rcases started with ⟨⟨⟨_ | born,shell⟩,control⟩,secret⟩
  · rw [←prEvent_eq_evalDist_of_discrete,prEvent_pure]
    exact bot_le
  · dsimp only
    rw [bind_pure_comp]
    rw [←prEvent_eq_evalDist_of_discrete,prEvent_map]
    simp only [decide_eq_true_eq]
    rw [prEvent_eq_evalDist_of_discrete]
    exact RegistrationNativePlatformOriginWarmSelectedPendingBound.attempts setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
      modes replace start virgin initialEmpty ideal (PqxdhRecordLiftBudget.recordBudget budget .raw) raw born shell control secret supported budget (bounded born)

/-- A genuine reduction sampler discharges the local initialization conditions at its SAME reached private state. Only the named observation normalization removes the uniform counter; no operational cache or state reset is assumed. -/
theorem sampled_bound {Sample : Type} (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes →Pqxdh.Bytes) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀born,RegistrationNativeInterface.Respects budget (work born))
    (sample : ProbComp Sample)
    (sampled : Sample × RegistrationNativePlatformLorIdealPhysical.State n (CtxPrivate n))
    (called : sampled∈support ((simulateQ
      (RegistrationNativePlatformLorIdealPhysical.implementation (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup concrete) concrete route)
      (simulateQ (PqxdhRecordLiftInterface.coinLift (n:=n)) sample)).run
        (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,CtxPrivate.initial))) :
    𝒟[RegistrationNativePlatformOriginInitializedCallback.program setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) (PqxdhRecordFactsCounter.zeroCtx sampled.2.2.2)]
      {result|result.2=true}≤budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  obtain ⟨virgin,empty⟩:=RegistrationNativePlatformRecordPartnerWarmKeys.sampler_initial modes replace setup concrete route sample sampled called
  apply bound setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
    (PqxdhRecordFactsCounter.zeroCtx sampled.2.2.2) _ _ modes ideal replace budget bounded
  · exact virgin
  · exact empty

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmInitializedCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmInitializedCallback.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmInitializedCallback.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmInitializedCallback.sampled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmInitializedCallback.sampled_bound
