-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarkerSource
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupLedgerTails
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer
/-! Genuine startup, the current native ledger, and any actual fresh-seal suffix retain selected replay markers on the same source execution. The established normalized private-cache observation remains explicit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftProtocol (ServiceSpec)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value : Type} {base : OracleSpec I}
variable (target : Label n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (env : RegistrationNativeHiddenStartup.Started source → RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : RegistrationNativeHiddenStartup.Started source → Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : RegistrationNativeHiddenStartup.Started source → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (initial : RegistrationNativeHiddenStartup.Started source → Platform)
local notation "world" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve codec bounds mode work initial
local notation "service" => PqxdhRecordFactsOriginMarkerNative.service target modes replace setup codec
local notation "compile" => RegistrationNativePlatformOriginStartupTails.compile codec route

private theorem compile_bind {A B : Type} (first : OracleComp (WorldSpec n) A)
    (next : A → OracleComp (WorldSpec n) B) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    compile (first >>= next) shell control =
      (do let result ← compile first shell control
          compile (next result.1.1) result.1.2 result.2) := by
  simp only [RegistrationNativePlatformOriginStartupTails.compile,simulateQ_bind,StateT.run_bind]

/-- Genuine startup and its born-dependent current native suffix derive all original received-entry marker facts without changing the reached shared-cache prefix. -/
theorem world_entryFacts (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n × Bool) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (result : ((RegistrationNativeEntropyRun.Outcome Platform Value × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result∈support ((simulateQ service (compile world shell control)).run secret)) :
    ∀finished∈result.1.1.1,∀entry∈finished.2.1.2.ledger.transcript,
      PqxdhRecordFactsOriginMarkerEntry.EntryFact target route result.1.2 result.2.2 entry := by
  unfold RegistrationNativePlatformOriginStartupLedgerTails.world at supported
  rw [compile_bind,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨born,called,continued⟩ := supported
  have safeBorn := (PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route
    ((simulateQ CborRecordWorldClient.handler (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run shell)
    control safe secret born called).1
  rcases born with ⟨⟨⟨_ | born,shellAfter⟩,controlAfter⟩,secretAfter⟩
  · simp only [RegistrationNativePlatformOriginStartupTails.compile,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
    subst result
    intro finished impossible
    cases impossible
  · exact RegistrationNativePlatformOriginGatedMarkerSource.program_entryFacts target modes replace setup codec route
      (env born) (reserve born) serverKeyId bounds mode (work born) born.created (initial born)
      shellAfter controlAfter secretAfter safeBorn result continued

/-- An accepted physical target in the original encoded result raises this same whole initialized source execution's marker. -/
theorem target_flag (secret : CtxPrivate n × Bool)
    (result : PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra Platform) Value × (CtxPrivate n × Bool))
    (supported : result∈support ((simulateQ service (RegistrationNativeRecordOriginProgram.program codec route world)).run secret))
    (accepted : PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget target route (result.1,result.2.1)) : result.2.2=true := by
  simp only [RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,PqxdhRecordLiftProtocol.schedule,
    CborRecordWorldClient.client,simulateQ_map,StateT.run_map,Functor.map_map,support_map] at supported
  obtain ⟨original,called,rfl⟩ := supported
  have facts := world_entryFacts target modes replace setup source ensureInit identityIndex serverKeyId identity env reserve codec route
    bounds mode work initial CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret
    PqxdhRecordLiftProtocolHistory.initial_safe original called
  obtain ⟨value,present,entry,member,receiver,raw,opened,handle,received,routed,slot,direction,position⟩ := accepted
  change value∈RegistrationNativeRecordPackage.encode original.1.1.1 at present
  rw [RegistrationNativeRecordPackage.encode,Option.mem_def,Option.map_eq_some_iff] at present
  obtain ⟨finished,finishedPresent,rfl⟩ := present
  exact (facts finished finishedPresent entry member receiver raw opened handle received routed).2 slot direction position

/-- Every marked source continuation at an actual fresh seal reconstructs this same initialized execution. Its original final acceptance therefore raises that suffix's marker. -/
theorem suffix_target_flag (ideal : ∀label,modes label≠.real)
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n (PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra Platform) Value))
    (earlier : List (PqxdhRecordFactsOriginOrdinalCut.Cut n (PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra Platform) Value)))
    (prefixPath : PqxdhRecordFactsOriginOrdinalPath.Prefix
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (RegistrationNativeRecordOriginProgram.program codec route world)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      (((ServiceSpec n).query (.sealing cut.pending) : OracleComp (ServiceSpec n) _) >>= cut.next) cut.state cut.past earlier)
    (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
    (answered : reply∈support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state))
    (result : PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra Platform) Value × (CtxPrivate n × Bool))
    (continued : result∈support ((simulateQ
      (PqxdhRecordFactsOriginMarkerNative.service cut.pending.material modes replace setup codec) (cut.next reply.1)).run (reply.2,false)))
    (accepted : PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget cut.pending.material route (result.1,result.2.1)) : result.2.2=true := by
  obtain ⟨cuts,flagged⟩ := PqxdhRecordFactsOriginOrdinalMarkedPath.support_flagged cut.pending.material
    (RawCtxUniversalDecoder.decoder codec.frameRead) (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (cut.next reply.1) reply.2 (cut.past++[cut.pending.material]) false result continued
  have empty := RegistrationNativeRecordOriginProgram.prefix_empty modes replace setup codec route world
    cut.pending cut.next cut.state cut.past (PqxdhRecordFactsOriginOrdinalPath.prefix_reach _ prefixPath)
  have whole := PqxdhRecordFactsOriginOrdinalPrefixFlag.sealing_prefix_false cut.pending.material codec.frameRead
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (fun query state output supported entry present => PqxdhRecordFactsOriginSealFacts.erased_service_mono
      modes ideal replace setup codec query state output supported cut.pending.material entry present)
    cut.pending cut.next prefixPath empty reply answered (cuts,(result.1,result.2.1)) result.2.2 flagged
  exact target_flag cut.pending.material modes replace setup source ensureInit identityIndex serverKeyId identity env reserve codec route
    bounds mode work initial (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial,false) result
    (PqxdhRecordFactsOriginOrdinalMarkedPath.flagged_support cut.pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) whole) accepted
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker.world_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker.world_entryFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker.target_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker.target_flag

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker.suffix_target_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker.suffix_target_flag
