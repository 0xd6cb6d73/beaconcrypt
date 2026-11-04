-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmInitializedCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedEventCover
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmEntrySequence
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAcceptedCover
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedPendingBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover
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



noncomputable local instance (p : Prop) : Decidable p:=Classical.propDecidable p
/-- The original temporal unpublished-accept event implies the bounded flag on the same genuine initialized warm execution. Every path, startup safety and sequence premise is derived internally. -/
theorem cover (start : CtxPrivate n) (initialEmpty : ∀label,(start.keys label).1.successfulSeals=[])
    (modes : Label n→KeyMode) (ideal : ∀label,modes label≠.real) (replace : Pqxdh.Bytes→Pqxdh.Bytes)
    (result : (Client n Platform Value×CtxPrivate n)×Bool)
    (supported : result∈support (RegistrationNativePlatformOriginInitializedCallback.program setup source ensureInit identityIndex serverKeyId identity
      env reserve route bounds mode work initial observe (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) start))
    (bad : PqxdhRecordLiftIdeal.UnpublishedAccept concrete route (PqxdhRecordLiftIdeal.ctxView result.1)) : result.2=true := by
  have original : result.1∈support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete)
      (RegistrationNativeRecordOriginProgram.program concrete route world)).run start) := by
    rw [←RegistrationNativePlatformOriginInitializedCallback.erase setup source ensureInit identityIndex serverKeyId identity
      env reserve route bounds mode work initial observe _ start,support_map]
    exact ⟨result,supported,rfl⟩
  have consistent:=RegistrationNativePlatformOriginWarmEntrySequence.run concrete route world
    (RegistrationNativeRecordOriginProgram.program concrete route world) id (by rw [id_map])
    modes ideal replace setup start initialEmpty result.1 original
  unfold RegistrationNativePlatformOriginInitializedCallback.program at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨started,startedCalled,continued⟩:=supported
  rcases started with ⟨⟨⟨_ | born,shell⟩,control⟩,secret⟩
  · rw [mem_support_pure_iff] at continued
    cases continued
    simp only [PqxdhRecordLiftIdeal.UnpublishedAccept,PqxdhRecordLiftIdeal.ctxView,PqxdhRecordLiftIdeal.viewOf,
      Option.map_none] at bad
    obtain ⟨value,impossible,_⟩:=bad
    cases impossible
  · dsimp only at continued
    rw [bind_pure_comp,support_map] at continued
    obtain ⟨body,called,rfl⟩:=continued
    have facts:=RegistrationNativePlatformOriginErasedStartup.facts modes replace setup concrete route source ensureInit
      identityIndex serverKeyId identity start (((some born,shell),control),secret) startedCalled
    have empty : ∀label,(secret.keys label).1.successfulSeals=[] := by
      intro label
      rw [facts.2]
      exact initialEmpty label
    have witnessed:=RegistrationNativePlatformOriginTrackedEventCover.tracked setup source serverKeyId env reserve route bounds mode work initial observe
      modes ideal replace born shell control secret facts.1 empty body called consistent bad
    exact decide_eq_true witnessed

local instance : MeasurableSpace (Client n Platform Value×CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (Client n Platform Value×CtxPrivate n) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace ((Client n Platform Value×CtxPrivate n)×Bool) := ⊤
local instance : DiscreteMeasurableSpace ((Client n Platform Value×CtxPrivate n)×Bool) := ⟨fun _=>trivial⟩
/-- The exact original warm erased source event has the coefficient-two bound, averaging all actual attempts and startup failures once. -/
theorem bound (start : CtxPrivate n) (virgin : PqxdhRecordFactsPrivateCacheSource.Virgin start [])
    (initialEmpty : ∀label,(start.keys label).1.successfulSeals=[])
    (modes : Label n→KeyMode) (ideal : ∀label,modes label≠.real) (replace : Pqxdh.Bytes→Pqxdh.Bytes)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀born,RegistrationNativeInterface.Respects budget (work born)) :
    Pr{let result←(simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete)
      (RegistrationNativeRecordOriginProgram.program concrete route world)).run start}[
        PqxdhRecordLiftIdeal.UnpublishedAccept concrete route (PqxdhRecordLiftIdeal.ctxView result)]≤
      budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  let observe : RegistrationNativeHiddenStartup.Started source→Front n Platform→Unit:=fun _ _=>()
  calc
    _=Pr{let result←RegistrationNativePlatformOriginInitializedCallback.program setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
          (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) start}[
        PqxdhRecordLiftIdeal.UnpublishedAccept concrete route (PqxdhRecordLiftIdeal.ctxView result.1)] := by
      rw [←RegistrationNativePlatformOriginInitializedCallback.erase setup source ensureInit identityIndex serverKeyId identity
        env reserve route bounds mode work initial observe _ start,prEvent_map]
    _≤Pr{let result←RegistrationNativePlatformOriginInitializedCallback.program setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
          (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) start}[result.2=true] := by
      apply prEvent_mono_of_support
      intro result supported bad
      exact cover setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
        start initialEmpty modes ideal replace result supported bad
    _=𝒟[RegistrationNativePlatformOriginInitializedCallback.program setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
          (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) start] {result|result.2=true} := prEvent_eq_evalDist_of_discrete _ _
    _≤_:=RegistrationNativePlatformOriginWarmInitializedCallback.bound setup source ensureInit identityIndex serverKeyId identity
      env reserve route bounds mode work initial observe start virgin initialEmpty modes ideal replace budget bounded


/-- The genuine physical sampler derives the local initialization facts for the original erased event bound at its same warmed state. Only the named uniform-counter normalization is applied. -/
theorem sampled_bound {Sample : Type} (modes : Label n→KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes→Pqxdh.Bytes) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀born,RegistrationNativeInterface.Respects budget (work born)) (sample : ProbComp Sample)
    (sampled : Sample×RegistrationNativePlatformLorIdealPhysical.State n (CtxPrivate n))
    (called : sampled∈support ((simulateQ
      (RegistrationNativePlatformLorIdealPhysical.implementation (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup concrete) concrete route)
      (simulateQ (PqxdhRecordLiftInterface.coinLift (n:=n)) sample)).run
        (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,CtxPrivate.initial))) :
    Pr{let result←(simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete)
      (RegistrationNativeRecordOriginProgram.program concrete route world)).run (PqxdhRecordFactsCounter.zeroCtx sampled.2.2.2)}[
        PqxdhRecordLiftIdeal.UnpublishedAccept concrete route (PqxdhRecordLiftIdeal.ctxView result)]≤
      budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  obtain ⟨virgin,empty⟩:=RegistrationNativePlatformRecordPartnerWarmKeys.sampler_initial modes replace setup concrete route sample sampled called
  exact bound setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial
    (PqxdhRecordFactsCounter.zeroCtx sampled.2.2.2) virgin empty modes ideal replace budget bounded

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover.cover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover.bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover.sampled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover.sampled_bound
