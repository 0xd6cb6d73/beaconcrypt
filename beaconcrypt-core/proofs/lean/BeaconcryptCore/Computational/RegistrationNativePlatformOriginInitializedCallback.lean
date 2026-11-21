-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedPendingBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginRawBudget
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback
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
local notation "front(" born ")" => RegistrationNativeObservedStageTrace.handler (observe born)
  (RegistrationNativePlatformOriginFreeFullTrace.frontend (RegistrationNativeEntropyPort.environment (env born))
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto concrete route serverKeyId bounds)
local notation "X" => (Client n Platform Value × Option (Option (RegistrationNativePlatformOriginCallbackFreeStop.PublicCall PqxdhDeploymentInterface.FullSpec) × Value)) × Calls View
local notation "S" => (Front n Platform × Calls View) × CtxPrivate n
local notation "counted" => RegistrationNativePlatformOriginSendCallbackBudget.Sending
local notation "compiled(" born ")" => RegistrationNativePlatformOriginSelectedProgram.compiled source mode work born
local notation "before(" born "," shell "," control "," privateBefore ")" =>
  (((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]),privateBefore)

noncomputable local instance (p : Prop) : Decidable p:=Classical.propDecidable p
local notation "event(" born ")" => RegistrationNativePlatformOriginSelectedPendingBound.event source route born

/-- A proof-only actual callback flag is retained beside the complete original source client and reached private state. -/
noncomputable def program (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) (initialPrivate : CtxPrivate n) :
    ProbComp ((Client n Platform Value × CtxPrivate n) × Bool) := do
  let started←(simulateQ service (compile (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl)).run initialPrivate
  match started.1.1.1 with
  | none=>pure (((none,started.1.2),started.2),false)
  | some born=>
    let result←RegistrationNativePlatformOriginCallbackTrace.track counted (QueryImpl.Stateful.link (front(born)) service)
      (compiled(born)) (before(born,started.1.1.2,started.1.2,started.2))
    pure ((RegistrationNativePlatformOriginJournalProgram.plain born.created (result.2.1,result.2.2.1.1),result.2.2.2),
      decide (∃current∈result.1,event(born) current result.2))

/-- Erasing only the annotation gives the SAME literal initialized source-client run and complete private poststate. No callback or origin law is assumed. -/
theorem erase (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) (initialPrivate : CtxPrivate n) :
    Prod.fst <$>program setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe service initialPrivate=
      (simulateQ service (RegistrationNativeRecordOriginProgram.program concrete route world)).run initialPrivate := by
  have erasure:=congrArg (fun tree=>(simulateQ service tree).run initialPrivate)
    (RegistrationNativePlatformOriginJournalProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve concrete route bounds mode work initial observe)
  simp only [simulateQ_map,StateT.run_map] at erasure
  rw [←erasure]
  unfold program RegistrationNativePlatformOriginJournalProgram.program
  simp only [map_bind,simulateQ_bind,StateT.run_bind]
  apply bind_congr
  rintro ⟨⟨⟨_ | born,shell⟩,control⟩,secret⟩
  · simp only [map_pure,simulateQ_pure,StateT.run_pure]
  · simp only [simulateQ_map,StateT.run_map,bind_pure_comp,Functor.map_map]
    have dropped:=congrArg (Functor.map (fun result:Value × ((Front n Platform × Calls View) × CtxPrivate n)=>
      (RegistrationNativePlatformOriginJournalProgram.plain born.created (result.1,result.2.1.1),result.2.2)))
      (RegistrationNativePlatformOriginCallbackTrace.track_drop counted (QueryImpl.Stateful.link (front(born)) service)
        (compiled(born)) (before(born,shell,control,secret)))
    rw [QueryImpl.Stateful.simulateQ_link_run] at dropped
    simpa only [Functor.map_map,RegistrationNativePlatformOriginJournalProgram.pack,QueryImpl.Stateful.Frame.prod,
      PFunctor.Lens.State.fst,PFunctor.Lens.State.snd,PFunctor.Lens.State.mk_put,RegistrationNativePlatformOriginSelectedProgram.compiled] using dropped
local instance : MeasurableSpace ((Client n Platform Value × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((Client n Platform Value × CtxPrivate n) × Bool) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (RegistrationNativePlatformOriginCallbackTrace.Result PqxdhDeploymentInterface.FullSpec S Value) := ⊤
local instance : DiscreteMeasurableSpace (RegistrationNativePlatformOriginCallbackTrace.Result PqxdhDeploymentInterface.FullSpec S Value) := ⟨fun _=>trivial⟩

/-- The whole genuine initialized source averages all startup failures and all attempted callback ordinals, deriving both original resource allowances internally. The same original complete outcome and reached private state remain beside the flag. -/
theorem bound (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes →Pqxdh.Bytes) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀born,RegistrationNativeInterface.Respects budget (work born)) :
    𝒟[program setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete) (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)]
      {result|result.2=true}≤budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  let service:=PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concrete
  have raw:=RegistrationNativePlatformOriginRawBudget.raw setup source ensureInit identityIndex serverKeyId identity env reserve concrete bounds mode work initial route budget bounded
  unfold program
  let : MeasurableSpace (((Option (RegistrationNativeHiddenStartup.Started source) × CborRecordWorldClient.Shell) × Control n) × CtxPrivate n) := ⊤
  let : DiscreteMeasurableSpace (((Option (RegistrationNativeHiddenStartup.Started source) × CborRecordWorldClient.Shell) × Control n) × CtxPrivate n) := ⟨fun _=>trivial⟩
  apply PqxdhRecordFactsOriginAverage.bind_le
  intro started supported
  rcases started with ⟨⟨⟨_ | born,shell⟩,control⟩,secret⟩
  · rw [←prEvent_eq_evalDist_of_discrete,prEvent_pure]
    exact bot_le
  · dsimp only
    rw [bind_pure_comp]
    rw [←prEvent_eq_evalDist_of_discrete,prEvent_map]
    simp only [decide_eq_true_eq]
    rw [prEvent_eq_evalDist_of_discrete]
    exact RegistrationNativePlatformOriginSelectedPendingBound.attempts setup source ensureInit identityIndex serverKeyId identity env reserve route bounds mode work initial observe
      modes replace ideal (PqxdhRecordLiftBudget.recordBudget budget .raw) raw born shell control secret supported budget (bounded born)

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedCallback.bound
