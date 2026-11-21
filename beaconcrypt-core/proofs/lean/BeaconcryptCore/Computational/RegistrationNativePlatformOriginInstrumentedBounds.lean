-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback
/-! Pure analysis journals inherit the original native source freshness and resource bills through their proved free return erasure, preserving the actual reserve statistic. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response E Value X Platform Failure : Type} {base : OracleSpec I}
variable (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (extended : OracleComp (ServiceSpec n) X)
    (erase : X → PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value)
    (erasure : erase <$>extended=RegistrationNativeRecordOriginProgram.program codec route work)

include erasure in
/-- Pure source-result instrumentation retains the original source-derived one-use sealing syntax. -/
theorem fresh : (PqxdhRecordLiftProtocolHistory.annotated extended []).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh := by
  have original := RegistrationNativeRecordOriginProgram.fresh codec route work
  rw [←erasure] at original
  simp only [PqxdhRecordLiftProtocolHistory.annotated,simulateQ_map,StateT.run_map] at original
  rw [allQueriesSatisfy_def,isQueryBound_map_iff] at original
  rw [allQueriesSatisfy_def]
  exact original

variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "start" => PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial (n := n))

include erasure in
/-- The instrumented source's same reached prefix derives actual unused private material. -/
theorem prefix_fresh (query : PqxdhRecordLiftProtocol.Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n))
    (called : PqxdhRecordFactsPrivateCacheSource.Reach service extended start []
      (((ServiceSpec n).query query : OracleComp (ServiceSpec n) _) >>= next) state past) :
    PqxdhRecordFactsPrivateCacheSource.FreshPoint state query := by
  have virgin := PqxdhRecordFactsPrivateCacheSource.reach_virgin modes replace setup codec
    PqxdhRecordFactsPrivateCacheSource.initial_virgin called
  have unused := PqxdhRecordFactsPrivateCacheSource.reach_fresh service (fresh codec route work extended erase erasure) called
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind,allQueriesSatisfy_query_bind_iff] at unused
  exact PqxdhRecordFactsPrivateCacheSource.freshPoint query state past virgin unused.1

include erasure in
/-- No ghost result coordinate can create an earlier selected seal in the actual reached dictionary. -/
theorem prefix_empty (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n))
    (called : PqxdhRecordFactsPrivateCacheSource.Reach service extended start []
      (((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _) >>= next) state past) :
    (state.keys pending.material).1.successfulSeals=[] := by
  have unused := PqxdhRecordFactsPrivateCacheSource.reach_fresh service (fresh codec route work extended erase erasure) called
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind,allQueriesSatisfy_query_bind_iff] at unused
  exact PqxdhRecordFactsOriginOrdinalReach.reach_unattempted_empty modes (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
    pending.material rfl called unused.1

section Concrete
local instance : MeasurableSpace ((X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((X × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩
local notation "concrete" => RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
/-- An actual erasing source journal has the same original reached-seal statistic, with all freshness and continuation caps derived through its proved free erasure. -/
theorem reached (actualWork : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (journal : OracleComp (ServiceSpec n) X)
    (project : X → PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value)
    (projected : project <$>journal=RegistrationNativeRecordOriginProgram.program concrete route actualWork)
    (rawCap : Nat)
    (bounded : (RegistrationNativeRecordOriginProgram.program concrete route actualWork).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (source : RegistrationNativePlatformOriginSourceTails.HasTails Platform Failure journal)
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n X) (ideal : modes cut.pending.material≠.real)
    (called : PqxdhRecordFactsPrivateCacheSource.Reach
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) journal
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      (((ServiceSpec n).query (.sealing cut.pending) : OracleComp (ServiceSpec n) _) >>= cut.next) cut.state cut.past) :
    ∃ (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
      (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) X)
      (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag),
      cut.next=RegistrationNativePlatformOriginReserveContinuationBound.continued reserve after before tag ∧
      𝒟[RegistrationNativePlatformOriginResumedCallback.sealingObservation reserve after before tag cut.pending.material
        (RawCtxUniversalDecoder.decoder (concrete).frameRead)
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) cut.state cut.pending]
        {result|result.2=true} ≤ 2*rawCap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  let actualService := PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete
  obtain ⟨reserve,after,before,tag,same⟩ := RegistrationNativePlatformOriginSourceTails.sealing_tail actualService source cut.pending cut.next called
  have unused := fresh concrete route actualWork journal project projected
  have freshPoint := prefix_fresh concrete route actualWork journal project projected modes replace setup _ _ _ _ called
  have empty := prefix_empty concrete route actualWork journal project projected modes replace setup _ _ _ _ called
  have remaining := PqxdhRecordFactsPrivateCacheSource.reach_fresh actualService unused called
  have noSeal := PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal cut.past cut.pending cut.next remaining
  have raws : journal.IsQueryBoundP (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap := by
    rw [←projected] at bounded
    simpa only [isQueryBoundP_map_iff] using bounded
  have suffix := PqxdhRecordFactsOriginRawBounds.reach_queries actualService _ rawCap raws called
  rw [isQueryBoundP_query_bind_iff] at suffix
  refine ⟨reserve,after,before,tag,same,?_⟩
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
end Concrete
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.prefix_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.prefix_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.prefix_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.prefix_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds.reached
