-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedFormBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedPendingBound
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
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete
local notation "front(" born ")" => RegistrationNativeObservedStageTrace.handler (observe born)
  (RegistrationNativePlatformOriginFreeFullTrace.frontend (RegistrationNativeEntropyPort.environment (env born))
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto concrete route serverKeyId bounds)
local notation "X" => (Client n Platform Value × Option (Option (RegistrationNativePlatformOriginCallbackFreeStop.PublicCall PqxdhDeploymentInterface.FullSpec) × Value)) × Calls View
local notation "S" => (Front n Platform × Calls View) × CtxPrivate n
local notation "counted" => RegistrationNativePlatformOriginSendCallbackBudget.Sending
local notation "compiled(" born ")" => RegistrationNativePlatformOriginSelectedProgram.compiled source mode work born
local notation "before(" born "," shell "," control "," privateBefore ")" =>
  (((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]),privateBefore)

def finish (born : RegistrationNativeHiddenStartup.Started source)
    (currentPublic : RegistrationNativePlatformOriginCallbackFreeStop.PublicCall PqxdhDeploymentInterface.FullSpec)
    (result : Value × (Front n Platform × Calls View)) : X :=
  RegistrationNativePlatformOriginSelectedStartupPrefix.pack source born ((some currentPublic,result.1),result.2)

def event (born : RegistrationNativeHiddenStartup.Started source)
    (current : RegistrationNativeStageTrace.Call PqxdhDeploymentInterface.FullSpec S) (final : Value × S) : Prop :=
  RegistrationNativePlatformOriginCallbackJoint.Event RegistrationNativePlatformOriginLedgerSendSyntax.reply
    (RegistrationNativePlatformOriginSelectedFormBound.accepted route) (finish source born) current final

local instance : MeasurableSpace (Option (RegistrationNativeStageTrace.Call PqxdhDeploymentInterface.FullSpec S) × (Value × S)) := ⊤
local instance : DiscreteMeasurableSpace (Option (RegistrationNativeStageTrace.Call PqxdhDeploymentInterface.FullSpec S) × (Value × S)) := ⟨fun _=>trivial⟩

/-- An actual initialized pending ordinal has the coefficient-two bound with its full same-source callback certificate and original adaptive future. All prefix, source form, and marker conditions are derived internally. -/
theorem pending (ideal : ∀label,modes label≠.real) (rawCap : Nat)
    (bounded : (RegistrationNativeRecordOriginProgram.program concrete route world).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (born : RegistrationNativeHiddenStartup.Started source) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (privateBefore : CtxPrivate n)
    (started : (((some born,shell),control),privateBefore)∈support
      ((simulateQ service (compile (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl)).run (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)))
    (index : Nat) (cut : RegistrationNativePlatformOriginCallbackCut.Cut PqxdhDeploymentInterface.FullSpec S Value)
    (selected : Sum.inr cut∈support (RegistrationNativePlatformOriginCallbackCut.scan counted
      (QueryImpl.Stateful.link (front(born)) service) (compiled(born)) index (before(born,shell,control,privateBefore)))) :
    𝒟[RegistrationNativePlatformOriginCallbackCut.markedResume (QueryImpl.Stateful.link (front(born)) service) (.inr cut)]
      {result|RegistrationNativePlatformOriginCallbackProbability.SelectedEvent (event source route born) result}
      ≤2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹ := by
  have charged:=(RegistrationNativePlatformOriginCallbackCut.scan_prefix counted (QueryImpl.Stateful.link (front(born)) service)
    (compiled(born)) index (before(born,shell,control,privateBefore)) cut selected).2
  obtain ⟨past,cuts,beforePrefix⟩:=RegistrationNativePlatformOriginSelectedStartupPrefix.pending setup source ensureInit identityIndex serverKeyId identity
    env reserve concrete route bounds mode work initial observe service (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)
    born shell control privateBefore started index cut selected
  let future:=fun returned:PqxdhDeploymentInterface.FullSpec.Range cut.query × (Front n Platform × Calls View)=>
    (finish source born ⟨cut.query,returned.1⟩) <$>(simulateQ (front(born)) (cut.next returned.1)).run returned.2
  have same : RegistrationNativePlatformOriginSelectedStartupPrefix.pack source born <$>
      (simulateQ (front(born)) (RegistrationNativePlatformOriginCallbackFreeStop.markedResume (.pending cut.query cut.next))).run cut.state.1=
      ((front(born) cut.query).run cut.state.1 >>=future) := by
    simp only [RegistrationNativePlatformOriginCallbackFreeStop.markedResume,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
      simulateQ_map,StateT.run_map,map_bind,bind_pure_comp,Functor.map_map,future]
    rfl
  rw [same] at beforePrefix
  have localBound:=RegistrationNativePlatformOriginSelectedFormBound.callback setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
    index modes replace ideal rawCap bounded born cut.query charged cut.state.1 future cut.state.2 past cuts beforePrefix
  have sameProbability:=RegistrationNativePlatformOriginCallbackJoint.probability (front(born)) service (finish source born) cut
    RegistrationNativePlatformOriginLedgerSendSyntax.reply (RegistrationNativePlatformOriginSelectedFormBound.accepted route)
  exact sameProbability.trans_le localBound
local instance : MeasurableSpace (RegistrationNativePlatformOriginCallbackTrace.Result PqxdhDeploymentInterface.FullSpec S Value) := ⊤
local instance : DiscreteMeasurableSpace (RegistrationNativePlatformOriginCallbackTrace.Result PqxdhDeploymentInterface.FullSpec S Value) := ⟨fun _=>trivial⟩

/-- All attempted server sends, beacon sends, tests and fresh requests contribute their original allowance ONCE; the full same-source acquired/refused/accepted event has coefficient two, with every failed history retained. -/
theorem attempts (ideal : ∀label,modes label≠.real) (rawCap : Nat)
    (bounded : (RegistrationNativeRecordOriginProgram.program concrete route world).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (born : RegistrationNativeHiddenStartup.Started source) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (privateBefore : CtxPrivate n)
    (started : (((some born,shell),control),privateBefore)∈support
      ((simulateQ service (compile (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl)).run (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)))
    (budget : PqxdhDeploymentInterface.Budget) (billed : RegistrationNativeInterface.Respects budget (work born)) :
    𝒟[RegistrationNativePlatformOriginCallbackTrace.track counted (QueryImpl.Stateful.link (front(born)) service)
      (compiled(born)) (before(born,shell,control,privateBefore))]
      {result|∃current∈result.1,event source route born current result.2}
      ≤budget.sends*(2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  apply RegistrationNativePlatformOriginCallbackProbability.any_callback_bound counted (QueryImpl.Stateful.link (front(born)) service)
    (compiled(born)) (before(born,shell,control,privateBefore)) (event source route born) budget.sends
    (2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹)
  · exact RegistrationNativePlatformOriginSendCallbackBudget.compiled mode (work born) budget billed
  · intro index cut selected
    exact pending setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe modes replace
      ideal rawCap bounded born shell control privateBefore started index.val cut selected

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedPendingBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedPendingBound.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedPendingBound.pending

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedPendingBound.attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedPendingBound.attempts
