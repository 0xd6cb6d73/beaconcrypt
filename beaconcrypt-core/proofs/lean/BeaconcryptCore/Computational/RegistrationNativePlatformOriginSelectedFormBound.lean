-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedFormBound
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

/-- The actual initialized selected public-client extension supplies its same-prefix marker implication internally. -/
theorem flags (ideal : ∀label,modes label≠.real) :
    RegistrationNativePlatformOriginSourceFormBound.Flags
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (RawCtxUniversalDecoder.decoder codec.frameRead)
      (fun label (result : X × CtxPrivate n)=>PqxdhRecordFactsOriginResumeConsumer.AcceptedTarget label route (result.1.1.1,result.2))
      journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) := by
  intro cut earlier beforePrefix sealed answered result continued accepted
  exact RegistrationNativePlatformOriginSelectedMarker.suffix_target_flag setup source ensureInit identityIndex serverKeyId identity env reserve codec route
    bounds mode work initial observe index modes replace ideal cut earlier beforePrefix sealed answered result continued accepted
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
theorem callback (ideal : ∀label,modes label≠.real) (rawCap : Nat)
    (bounded : (RegistrationNativeRecordOriginProgram.program concrete route actualWorld).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (born : RegistrationNativeHiddenStartup.Started source) (request : PqxdhDeploymentInterface.FullSpec.Domain)
    (counted : RegistrationNativePlatformOriginSendCallbackBudget.Sending request)
    (beforeFront : Front n Platform × Calls View)
    (future : PqxdhDeploymentInterface.FullSpec.Range request × (Front n Platform × Calls View) →OracleComp (ServiceSpec n) X)
    (before : CtxPrivate n) (past : List (Label n)) (cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (beforePrefix : PqxdhRecordFactsOriginOrdinalPath.Prefix actualService actualJournal
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((front(born) request).run beforeFront >>=future) before past cuts) :
    𝒟[RegistrationNativePlatformOriginSourceFormBound.run actualService
      ((front(born) request).run beforeFront) future before]
      {result|RegistrationNativePlatformOriginSourceFormBound.Bad
        (fun result=>RegistrationNativePlatformOriginLedgerSendSyntax.reply request result.1) actualAccepts before result}
      ≤2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹ := by
  exact RegistrationNativePlatformOriginSourceFormBound.bound route modes ideal replace setup actualWorld actualJournal
    (fun result=>result.1.1)
    (RegistrationNativePlatformOriginSelectedProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe index)
    rawCap bounded (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) _ actualAccepts _
    (RegistrationNativePlatformOriginFrontendForm.observed (RegistrationNativeEntropyPort.environment (env born))
      (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto concrete route serverKeyId bounds
      (observe born) request counted beforeFront)
    future before past cuts beforePrefix
    (flags setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe index modes replace ideal)

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedFormBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedFormBound.flags' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedFormBound.flags

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedFormBound.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedFormBound.callback
