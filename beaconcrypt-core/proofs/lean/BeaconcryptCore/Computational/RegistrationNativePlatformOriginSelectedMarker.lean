-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedMarker
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
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : RegistrationNativeHiddenStartup.Started source → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (initial : RegistrationNativeHiddenStartup.Started source → Platform)
    (observe : RegistrationNativeHiddenStartup.Started source → Front n Platform → View)
local notation "compile" => RegistrationNativePlatformOriginStartupTails.compile codec route
local notation "world" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve codec bounds mode work initial


variable (index : Nat) (target : Label n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
local notation "service" => PqxdhRecordFactsOriginMarkerNative.service target modes replace setup codec
local notation "journal" => RegistrationNativePlatformOriginSelectedProgram.program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index
local notation "X" => (Client n Platform Value × Option (Option (RegistrationNativePlatformOriginCallbackFreeStop.PublicCall PqxdhDeploymentInterface.FullSpec) × Value)) × Calls View

/-- The actual same initialized journal's original client acceptance raises its own marker; no journal or callback-origin premise is assumed. -/
theorem target_flag (secret : CtxPrivate n × Bool) (result : X × (CtxPrivate n × Bool))
    (supported : result∈support ((simulateQ service journal).run secret))
    (accepted : PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget target route (result.1.1.1,result.2.1)) :result.2.2=true := by
  have erased :=congrArg (fun tree=>(simulateQ service tree).run secret)
    (RegistrationNativePlatformOriginSelectedProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index)
  simp only [simulateQ_map,StateT.run_map] at erased
  have called : (result.1.1.1,result.2)∈support ((simulateQ service (RegistrationNativeRecordOriginProgram.program codec route world)).run secret) := by
    rw [←erased,support_map]
    exact ⟨result,supported,rfl⟩
  exact RegistrationNativePlatformOriginStartupMarker.target_flag target modes replace setup source ensureInit identityIndex serverKeyId identity
    env reserve codec route bounds mode work initial secret _ called accepted

/-- The literal initialized journal prefix and selected seal reconstruct that same complete marked execution; the original acceptance flags this same suffix. -/
theorem suffix_target_flag (ideal : ∀label,modes label≠.real)
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n X)
    (earlier : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (prefixPath : PqxdhRecordFactsOriginOrdinalPath.Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      (((ServiceSpec n).query (.sealing cut.pending) : OracleComp (ServiceSpec n) _) >>=cut.next) cut.state cut.past earlier)
    (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
    (answered : reply∈support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state))
    (result : X × (CtxPrivate n × Bool))
    (continued : result∈support ((simulateQ
      (PqxdhRecordFactsOriginMarkerNative.service cut.pending.material modes replace setup codec) (cut.next reply.1)).run (reply.2,false)))
    (accepted : PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget cut.pending.material route (result.1.1.1,result.2.1)) :result.2.2=true := by
  obtain ⟨cuts,flagged⟩ :=PqxdhRecordFactsOriginOrdinalMarkedPath.support_flagged cut.pending.material
    (RawCtxUniversalDecoder.decoder codec.frameRead) (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (cut.next reply.1) reply.2 (cut.past++[cut.pending.material]) false result continued
  have empty :=RegistrationNativePlatformOriginInstrumentedBounds.prefix_empty codec route world journal (fun result=>result.1.1)
    (RegistrationNativePlatformOriginSelectedProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index)
    modes replace setup cut.pending cut.next cut.state cut.past (PqxdhRecordFactsOriginOrdinalPath.prefix_reach _ prefixPath)
  have whole :=PqxdhRecordFactsOriginOrdinalPrefixFlag.sealing_prefix_false cut.pending.material codec.frameRead
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (fun query state output supported entry present=>PqxdhRecordFactsOriginSealFacts.erased_service_mono
      modes ideal replace setup codec query state output supported cut.pending.material entry present)
    cut.pending cut.next prefixPath empty reply answered (cuts,(result.1,result.2.1)) result.2.2 flagged
  exact target_flag setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe
    index cut.pending.material modes replace (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial,false) result
    (PqxdhRecordFactsOriginOrdinalMarkedPath.flagged_support cut.pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) whole) accepted
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedMarker

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedMarker.target_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedMarker.target_flag


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedMarker.suffix_target_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedMarker.suffix_target_flag
