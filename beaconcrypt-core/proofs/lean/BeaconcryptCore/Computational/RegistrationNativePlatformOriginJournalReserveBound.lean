-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProperties
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGivenReserveBound
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalReserveBound
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativePlatformOriginJournalProgram (Front Calls Client)
variable {n : Nat} {I KemSK Platform Failure Value View : Type} {base : OracleSpec I}
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
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
local notation "concrete" => RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
local notation "world" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve concrete bounds mode work initial
local notation "journal" => RegistrationNativePlatformOriginJournalProgram.program setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete
local notation "X" => Client n Platform Value × Calls View
local instance : MeasurableSpace ((X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((X × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩

/-- The literal genuine-startup/full-ledger journal gives the specified actual reserve future its reached-seal bound, with no caller erasure, freshness, history, or hypothetical-platform cap premise. -/
theorem reached (rawCap : Nat)
    (bounded : (RegistrationNativeRecordOriginProgram.program concrete route world).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n X) (ideal : modes cut.pending.material≠.real)
    (called : PqxdhRecordFactsPrivateCacheSource.Reach service journal
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      (((ServiceSpec n).query (.sealing cut.pending) : OracleComp (ServiceSpec n) _) >>= cut.next) cut.state cut.past)
    (actualReserve : Nat → StateT (RegistrationNativeEntropyPort.State Platform) ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → RegistrationNativeEntropyPort.State Platform → OracleComp (ServiceSpec n) X)
    (beforeP : RegistrationNativeEntropyPort.State Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (head : cut.next=RegistrationNativePlatformOriginReserveContinuationBound.continued actualReserve after beforeP tag) :
    𝒟[RegistrationNativePlatformOriginResumedCallback.sealingObservation actualReserve after beforeP tag cut.pending.material
      (RawCtxUniversalDecoder.decoder (concrete).frameRead) service cut.state cut.pending]
      {result|result.2=true} ≤2*rawCap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  exact RegistrationNativePlatformOriginGivenReserveBound.reached route modes replace setup world journal Prod.fst
    (RegistrationNativePlatformOriginJournalProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe)
    rawCap bounded cut ideal called actualReserve after beforeP tag head
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalReserveBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalReserveBound.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalReserveBound.reached
