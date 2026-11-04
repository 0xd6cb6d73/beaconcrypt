-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmReserveBound
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK E Value X Platform Failure : Type} {base : OracleSpec I}
variable (route : RawCtxServerRouting.SenderDecoder)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
local instance : MeasurableSpace ((X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((X × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩
local notation "concrete" => RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
/-- At an actual reached source seal, the specified literal reserve/future has the original coefficient-two raw bound; no hypothetical platform state or future cap is assumed. -/
theorem reached (actualWork : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (journal : OracleComp (ServiceSpec n) X)
    (project : X → PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value)
    (projected : project <$>journal=RegistrationNativeRecordOriginProgram.program concrete route actualWork)
    (start : CtxPrivate n) (virgin : PqxdhRecordFactsPrivateCacheSource.Virgin start [])
    (initialEmpty : ∀label,(start.keys label).1.successfulSeals=[])
    (rawCap : Nat)
    (bounded : (RegistrationNativeRecordOriginProgram.program concrete route actualWork).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n X) (ideal : modes cut.pending.material≠.real)
    (called : PqxdhRecordFactsPrivateCacheSource.Reach
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) journal
      start []
      (((ServiceSpec n).query (.sealing cut.pending) : OracleComp (ServiceSpec n) _) >>= cut.next) cut.state cut.past) :
    ∀ (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
      (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) X)
      (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag),
      cut.next=RegistrationNativePlatformOriginReserveContinuationBound.continued reserve after before tag →
      𝒟[RegistrationNativePlatformOriginResumedCallback.sealingObservation reserve after before tag cut.pending.material
        (RawCtxUniversalDecoder.decoder (concrete).frameRead)
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) cut.state cut.pending]
        {result|result.2=true} ≤ 2*rawCap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  let actualService := PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete
  intro reserve after before tag same
  have unused := RegistrationNativePlatformOriginInstrumentedBounds.fresh concrete route actualWork journal project projected
  have freshPoint := RegistrationNativePlatformOriginWarmPrefixFacts.prefix_fresh concrete route actualWork journal project projected modes replace setup start virgin _ _ _ _ called
  have empty := RegistrationNativePlatformOriginWarmPrefixFacts.prefix_empty concrete route actualWork journal project projected modes replace setup start cut.pending (initialEmpty cut.pending.material) _ _ _ called
  have remaining := PqxdhRecordFactsPrivateCacheSource.reach_fresh actualService unused called
  have noSeal := PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal cut.past cut.pending cut.next remaining
  have raws : journal.IsQueryBoundP (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap := by
    rw [←projected] at bounded
    simpa only [isQueryBoundP_map_iff] using bounded
  have suffix := PqxdhRecordFactsOriginRawBounds.reach_queries actualService _ rawCap raws called
  rw [isQueryBoundP_query_bind_iff] at suffix
  rw [RegistrationNativePlatformOriginResumedCallback.sealing_probability]
  apply RegistrationNativePlatformOriginReserveCallback.concrete_bound reserve (after none) before tag modes setup replace cut.pending cut.state ideal freshPoint empty
  · intro body absent
    apply RegistrationNativePlatformOriginReserveContinuationBound.fixed_bound reserve after before tag _ 0 _ _ absent
    intro reply
    rw [←same]
    exact noSeal reply
  · intro body absent
    apply RegistrationNativePlatformOriginReserveContinuationBound.fixed_bound reserve after before tag _ rawCap _ _ absent
    intro reply
    rw [←same]
    exact (suffix.2 reply).mono (by split_ifs <;> omega)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmReserveBound


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmReserveBound.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmReserveBound.reached
