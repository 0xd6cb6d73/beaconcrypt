-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds
/-! Instrumented original source prefixes retain freshness from the actual warm private start; only local virginity and empty selected seals are required. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response E Value X : Type} {base : OracleSpec I}
variable (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (extended : OracleComp (ServiceSpec n) X)
    (erase : X → PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value)
    (erasure : erase <$>extended=RegistrationNativeRecordOriginProgram.program codec route work)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
include erasure in
/-- The same instrumented source prefix is fresh from an arbitrary warm private state satisfying the actual local virgin invariant. -/
theorem prefix_fresh (start : CtxPrivate n) (virgin : PqxdhRecordFactsPrivateCacheSource.Virgin start [])
    (query : PqxdhRecordLiftProtocol.Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n))
    (called : PqxdhRecordFactsPrivateCacheSource.Reach service extended start []
      (((ServiceSpec n).query query : OracleComp (ServiceSpec n) _) >>=next) state past) :
    PqxdhRecordFactsPrivateCacheSource.FreshPoint state query := by
  have kept := PqxdhRecordFactsPrivateCacheSource.reach_virgin modes replace setup codec virgin called
  have unused := PqxdhRecordFactsPrivateCacheSource.reach_fresh service
    (RegistrationNativePlatformOriginInstrumentedBounds.fresh codec route work extended erase erasure) called
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind,allQueriesSatisfy_query_bind_iff] at unused
  exact PqxdhRecordFactsPrivateCacheSource.freshPoint query state past kept unused.1

include erasure in
/-- The actual unused coordinate still has its initially empty seal history without resetting the warm base, counters or cache. -/
theorem prefix_empty (start : CtxPrivate n) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (empty : (start.keys pending.material).1.successfulSeals=[])
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n))
    (called : PqxdhRecordFactsPrivateCacheSource.Reach service extended start []
      (((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _) >>=next) state past) :
    (state.keys pending.material).1.successfulSeals=[] := by
  have unused := PqxdhRecordFactsPrivateCacheSource.reach_fresh service
    (RegistrationNativePlatformOriginInstrumentedBounds.fresh codec route work extended erase erasure) called
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind,allQueriesSatisfy_query_bind_iff] at unused
  exact PqxdhRecordFactsOriginOrdinalReach.reach_unattempted_empty modes (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
    pending.material empty called unused.1
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts.prefix_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts.prefix_fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts.prefix_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts.prefix_empty
