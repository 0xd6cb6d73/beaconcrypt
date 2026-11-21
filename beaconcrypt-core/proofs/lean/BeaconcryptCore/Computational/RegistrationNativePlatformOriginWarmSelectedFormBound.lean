-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmFormBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmPrefixFacts
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedMarker
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedStartupPrefix
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound
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

theorem suffix_target_flag (start : CtxPrivate n) (initialEmpty : ∀label,(start.keys label).1.successfulSeals=[]) (ideal : ∀label,modes label≠.real)
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n X)
    (earlier : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (prefixPath : PqxdhRecordFactsOriginOrdinalPath.Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      journal start []
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
  have empty :=RegistrationNativePlatformOriginWarmPrefixFacts.prefix_empty codec route world journal (fun result=>result.1.1)
    (RegistrationNativePlatformOriginSelectedProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index)
    modes replace setup start cut.pending (initialEmpty cut.pending.material) cut.next cut.state cut.past (PqxdhRecordFactsOriginOrdinalPath.prefix_reach _ prefixPath)
  have whole :=PqxdhRecordFactsOriginOrdinalPrefixFlag.sealing_prefix_false cut.pending.material codec.frameRead
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (fun query state output supported entry present=>PqxdhRecordFactsOriginSealFacts.erased_service_mono
      modes ideal replace setup codec query state output supported cut.pending.material entry present)
    cut.pending cut.next prefixPath empty reply answered (cuts,(result.1,result.2.1)) result.2.2 flagged
  exact RegistrationNativePlatformOriginSelectedMarker.target_flag setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe
    index cut.pending.material modes replace (start,false) result
    (PqxdhRecordFactsOriginOrdinalMarkedPath.flagged_support cut.pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) whole) accepted

/-- The actual initialized selected public-client extension supplies its same-prefix marker implication internally. -/
theorem flags (start : CtxPrivate n) (initialEmpty : ∀label,(start.keys label).1.successfulSeals=[]) (ideal : ∀label,modes label≠.real) :
    RegistrationNativePlatformOriginSourceFormBound.Flags
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (RawCtxUniversalDecoder.decoder codec.frameRead)
      (fun label (result : X × CtxPrivate n)=>PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget label route (result.1.1.1,result.2))
      journal start := by
  intro cut earlier beforePrefix sealed answered result continued accepted
  exact suffix_target_flag setup source ensureInit identityIndex serverKeyId identity env reserve codec route
    bounds mode work initial observe index modes replace start initialEmpty ideal cut earlier beforePrefix sealed answered result continued accepted
local notation "concrete" => RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
local notation "actualWorld" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve concrete bounds mode work initial
local notation "actualJournal" => RegistrationNativePlatformOriginSelectedProgram.program setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe index
local notation "actualService" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete
local notation "front(" born ")" => RegistrationNativeObservedStageTrace.handler (observe born)
  (RegistrationNativePlatformOriginFreeFullTrace.frontend (RegistrationNativeEntropyPort.environment (env born))
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto concrete route serverKeyId bounds)
def accepted (label : Label n) (result : X × CtxPrivate n) : Prop :=
  PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget label route (result.1.1.1,result.2)
local notation "actualAccepts" => accepted route
local instance (A : Type) : MeasurableSpace (RegistrationNativePlatformOriginSourceFormBound.Joint n A X) := ⊤
local instance (A : Type) : DiscreteMeasurableSpace (RegistrationNativePlatformOriginSourceFormBound.Joint n A X) := ⟨fun _=>trivial⟩

/-- The complete actual frontend callback inherits the local coefficient-two bound; its source form and marked-future receipt are both derived from the literal initialized program. -/
theorem callback (start : CtxPrivate n) (virgin : PqxdhRecordFactsPrivateCacheSource.Virgin start [])
    (initialEmpty : ∀label,(start.keys label).1.successfulSeals=[]) (ideal : ∀label,modes label≠.real) (rawCap : Nat)
    (bounded : (RegistrationNativeRecordOriginProgram.program concrete route actualWorld).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (born : RegistrationNativeHiddenStartup.Started source) (request : PqxdhDeploymentInterface.FullSpec.Domain)
    (counted : RegistrationNativePlatformOriginSendCallbackBudget.Sending request)
    (beforeFront : Front n Platform × Calls View)
    (future : PqxdhDeploymentInterface.FullSpec.Range request × (Front n Platform × Calls View) →OracleComp (ServiceSpec n) X)
    (before : CtxPrivate n) (past : List (Label n)) (cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (beforePrefix : PqxdhRecordFactsOriginOrdinalPath.Prefix actualService actualJournal
      start []
      ((front(born) request).run beforeFront >>=future) before past cuts) :
    𝒟[RegistrationNativePlatformOriginSourceFormBound.run actualService
      ((front(born) request).run beforeFront) future before]
      {result|RegistrationNativePlatformOriginSourceFormBound.Bad
        (fun result=>RegistrationNativePlatformOriginLedgerSendSyntax.reply request result.1) actualAccepts before result}
      ≤2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹ := by
  exact RegistrationNativePlatformOriginWarmFormBound.bound route modes ideal replace setup actualWorld actualJournal
    (fun result=>result.1.1)
    (RegistrationNativePlatformOriginSelectedProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe index)
    start virgin initialEmpty rawCap bounded (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) _ actualAccepts _
    (RegistrationNativePlatformOriginFrontendForm.observed (RegistrationNativeEntropyPort.environment (env born))
      (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto concrete route serverKeyId bounds
      (observe born) request counted beforeFront)
    future before past cuts beforePrefix
    (flags setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe index modes replace start initialEmpty ideal)

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound.suffix_target_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound.suffix_target_flag

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound.flags' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound.flags

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginWarmSelectedFormBound.callback
