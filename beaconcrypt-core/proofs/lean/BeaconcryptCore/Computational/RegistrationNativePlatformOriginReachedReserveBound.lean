-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceCut
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback
/-! The original reached source prefix discharges every stopped-tail syntactic cap and selected dictionary premise in the actual reserve callback bound. The numeric service uses its explicit uniform-instrumentation observation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReachedReserveBound
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRecordOriginProgram (program)
open RegistrationNativeRecordPackage (Extra)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
variable {n : Nat} {I KemSK E Value Platform Failure : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (route : RawCtxServerRouting.SenderDecoder)
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
variable (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
local notation "Client" => PqxdhRecordLiftIdeal.Client n (Extra E) Value
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "start" => PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial (n := n))

/-- The same original source prefix supplies the exact gate future, zero repeated selected seals, raw cap and fresh dictionary. No bound at hypothetical platform values is assumed. -/
theorem reached (rawCap : Nat)
    (raws : (program codec route work).IsQueryBoundP (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (source : RegistrationNativePlatformOriginSourceTails.HasTails Platform Failure (program codec route work))
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n Client) (ideal : modes cut.pending.material≠.real)
    (called : PqxdhRecordFactsPrivateCacheSource.Reach service (program codec route work) start []
      (((ServiceSpec n).query (.sealing cut.pending) : OracleComp (ServiceSpec n) _) >>= cut.next) cut.state cut.past) :
    ∃ (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
      (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) Client)
      (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag),cut.next=continued reserve after before tag ∧
      𝒟[RegistrationNativePlatformOriginReserveCallback.callback reserve (after none) before tag modes setup codec replace cut.pending cut.state]
        {flag | flag=true} ≤ 2*rawCap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  obtain ⟨reserve,after,before,tag,same⟩ := RegistrationNativePlatformOriginSourceTails.sealing_tail service source cut.pending cut.next called
  have fresh := RegistrationNativeRecordOriginProgram.prefix_fresh modes replace setup codec route work (.sealing cut.pending) cut.next cut.state cut.past called
  have empty := RegistrationNativeRecordOriginProgram.prefix_empty modes replace setup codec route work cut.pending cut.next cut.state cut.past called
  have remaining := PqxdhRecordFactsPrivateCacheSource.reach_fresh service (RegistrationNativeRecordOriginProgram.fresh codec route work) called
  have noSeal : ∀reply,(cut.next reply).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing cut.pending.material) 0 :=
    PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal cut.past cut.pending cut.next remaining
  have rawSuffix := PqxdhRecordFactsOriginRawBounds.reach_queries service _ rawCap raws called
  rw [isQueryBoundP_query_bind_iff] at rawSuffix
  refine ⟨reserve,after,before,tag,same,?_⟩
  apply RegistrationNativePlatformOriginReserveCallback.concrete_bound reserve (after none) before tag modes setup replace cut.pending cut.state ideal fresh empty
  · intro body absent
    apply RegistrationNativePlatformOriginReserveContinuationBound.fixed_bound reserve after before tag _ 0 _ _ absent
    intro reply
    rw [←same]
    exact noSeal reply
  · intro body absent
    apply RegistrationNativePlatformOriginReserveContinuationBound.fixed_bound reserve after before tag _ rawCap _ _ absent
    intro reply
    rw [←same]
    exact (rawSuffix.2 reply).mono (by split_ifs <;> omega)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReachedReserveBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReachedReserveBound.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReachedReserveBound.reached
