-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionIdealAttachment
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmStage
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource
/-! The original pin-filtered public session event on the actual complete warm joint source is bounded by its physical record failure mass and Exposure on one genuine Word source experiment. Successful sessions and parsed accept selectors remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
open RegistrationNativePlatformG3UniformRecordProgram (sample)
variable (budget : PqxdhDeploymentInterface.Budget)
    (target : Fin budget.accept×Fin budget.capacity) (previous : Platform)
local notation "wire"=>RegistrationNativePlatformConcreteSource.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "cap"=>budget.cap 4+budget.cap 5
local notation "job"=>RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId (Fin.val (Prod.fst target))
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget (Prod.snd target) previous
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "service" => PqxdhRecordLiftIdeal.ctxInterpreter (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) id setup codec
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route


open RegistrationNativePlatformRecordSessionTargets (Kind)
abbrev Result :=RegistrationNativeEntropyRun.Outcome
  (RegistrationNativePlatformSelectiveEntropyEnvironment.State cap KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value ×
  (RegistrationNativePlatformPublicRecordSlots.State cap×RegistrationNativeG2Trace.State×
    RegistrationNativePlatformLorIdealPhysical.State cap (PqxdhRecordLiftIdeal.CtxPrivate cap))

def recordView (result : Result (KemSK:=KemSK) (Platform:=Platform) (Value:=Value) source budget) :=
  PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced

def PhysicalBad (kind : Kind) (result : Result (KemSK:=KemSK) (Platform:=Platform) (Value:=Value) source budget) : Prop :=
  match kind with
  | .origin _=>PqxdhRecordLiftIdeal.UnpublishedAccept codec route (recordView source budget result)
  | _=>PqxdhRecordLiftIdeal.CrossAccept codec route (recordView source budget result)

def Mismatch (result : Result (KemSK:=KemSK) (Platform:=Platform) (Value:=Value) source budget) : Prop :=
  ∃finished∈result.1,∃session:Fin budget.accept,
    RegistrationNativeParsedTargetCanonical.AcceptedAt canonical finished.2.1.2.transcript session.val target.1.val ∧
      RegistrationNativePlatformRecordPartnerEvents.Mismatch budget (session,target.2) finished.2.1.2.ledger.transcript
        (PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.1)

def Pinned (kind : Kind) (result : Result (KemSK:=KemSK) (Platform:=Platform) (Value:=Value) source budget) : Prop :=
  RegistrationNativePlatformG3UniformOpaqueRecord.event source
    (RegistrationNativePlatformRecordSessionTargets.pinnedEvent setup.source.crypto canonical serverKeyId budget route kind target)
    (RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced)=true

/-- The original public event on this same joint outcome splits into physical failure or its same-session mismatch, with no test/freshness restriction. -/
theorem outcome (bounded : ∀publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (result : Result (KemSK:=KemSK) (Platform:=Platform) (Value:=Value) source budget) (supported : result∈support job)
    (kind : Kind) (pinned : Pinned setup route source serverKeyId budget target kind result) :
    PhysicalBad route source budget kind result ∨Mismatch source budget target result := by
  cases value : result.1 with
  | none=>
    simp only [Pinned,RegistrationNativePlatformG3UniformOpaqueRecord.event,RegistrationNativePlatformG3UniformOpaqueRecord.outcomeEvent,
      RegistrationNativeRecordPackage.nativeView,value,Bool.false_eq_true] at pinned
  | some finished=>
    have present : finished∈result.1 := by rw [value];rfl
    have original : RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto canonical serverKeyId budget route kind target finished.2.1 := by
      simpa only [Pinned,RegistrationNativePlatformG3UniformOpaqueRecord.event,RegistrationNativePlatformG3UniformOpaqueRecord.outcomeEvent,
        RegistrationNativeRecordPackage.nativeView,value,RegistrationNativePlatformRecordSessionTargets.pinnedEvent,decide_eq_true_eq] using pinned
    obtain ⟨priorList,entry,later,session,ledger,witness,accepted,physicalBad|mismatch⟩:=
      RegistrationNativePlatformRecordSessionIdealAttachment.initialized setup checks source view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
        serverKeyId bounds mode budget target route ensureInit identityIndex previous adversary bounded result supported finished present kind original
    · left
      cases kind with
      | origin direction=>
        refine ⟨(finished.2.1.1,finished.2.1.2.ledger,(finished.1,finished.2.1.2.transcript,finished.2.2)),?_,priorList,entry,later,ledger,physicalBad⟩
        simp only [recordView,PqxdhRecordLiftIdeal.viewOf,RegistrationNativeRecordPackage.encode,value,Option.map_some,Option.mem_some_iff]
      | receiver=>exact physicalBad
      | sender=>exact physicalBad
    · exact Or.inr ⟨finished,present,session,accepted,mismatch⟩


local notation "unused"=>fun (_ : RegistrationNativeSuffixKeyPrf.Secret)=>RegistrationNativePlatformLorIdealSelected.unused (n:=cap)
local notation "wordGame"=>RegistrationNativePlatformRecordPartnerExposureWarm.wordGame setup checks wire route source
  ensureInit identityIndex serverKeyId (Fin.val (Prod.fst target)) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  bounds mode adversary budget (Prod.snd target) previous unused
local notation "PhysicalState"=>RegistrationNativePlatformLorIdealPhysical.State cap (PqxdhRecordLiftIdeal.CtxPrivate cap)

/-- The actual complete sampler/startup mismatch mass is bounded by Exposure on the one genuine warm Word experiment. No prefix or Word lift is selected from a later bad event. -/
theorem mismatch_bound :
    Pr{let result←job}[Mismatch source budget target result]≤Pr{let flag←wordGame}[flag=true] := by
  let : MeasurableSpace (RegistrationNativePlatformG3UniformRecordProgram.Sample KemSK cap×PhysicalState):=⊤
  let : DiscreteMeasurableSpace (RegistrationNativePlatformG3UniformRecordProgram.Sample KemSK cap×PhysicalState):=⟨fun _=>trivial⟩
  let : MeasurableSpace (Option (RegistrationNativeHiddenStartup.Started source)×PhysicalState):=⊤
  let : DiscreteMeasurableSpace (Option (RegistrationNativeHiddenStartup.Started source)×PhysicalState):=⟨fun _=>trivial⟩
  unfold RegistrationNativePlatformRecordPartnerJointUniform.joint RegistrationNativePlatformRecordPartnerExposureWarm.wordGame
  apply prEvent_bind_mono_of_forall_le_of_support
  intro parameters sampled
  have free : parameters.1∈support (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget target.2) := by
    have inner : parameters.1∈support (simulateQ (PqxdhRecordLiftInterface.coinLift (n:=cap))
        (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget target.2)) := by
      apply OracleComp.support_simulateQ_run'_subset physical _
        (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial)
      rw [StateT.run'_eq,support_map]
      exact ⟨parameters,sampled,rfl⟩
    exact PqxdhDeploymentEnvironment.support_simulateQ_subset (PqxdhRecordLiftInterface.coinLift (n:=cap)) _ inner
  obtain ⟨_reserved,chosen,_chosenAt,chosenPublic⟩:=RegistrationNativePlatformG3UniformRecordSample.sample_selected setup budget target.2 parameters.1 free
  have frame:=RegistrationNativePlatformRecordPartnerSampler.frame service codec route (sample setup budget target.2)
    (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial) parameters sampled
  have same : parameters.2=(CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,parameters.2.2.2) :=
    Prod.ext frame.1 (Prod.ext frame.2 rfl)
  rw [same]
  unfold RegistrationNativePlatformRecordPartnerJointStartup.joint RegistrationNativePlatformRecordPartnerExposureWarm.future
  simp only [bind_assoc,pure_bind]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro started startup
  cases built : started.1 with
  | none=>
    simp [RegistrationNativePlatformRecordPartnerExposureAveraged.after,Mismatch]
  | some born=>
    have named : (some born,started.2)∈support ((simulateQ physical
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys parameters.1.seed))).run
          (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,parameters.2.2.2)) := by
      simpa only [←built,Prod.mk.eta] using startup
    have stage:=RegistrationNativePlatformRecordPartnerWordWarmStage.bound setup checks source ensureInit identityIndex serverKeyId target.1.val
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds mode adversary budget target.2 previous
      service codec route parameters.1 chosen chosenPublic parameters.2.2.2 born started.2 named target.2 rfl
    simp only [Option.map_some,prEvent_map]
    apply le_trans ?_ stage
    apply prEvent_mono
    intro result mismatch
    obtain ⟨finished,present,session,accepted,mismatched⟩:=mismatch
    have sameFinished:=Option.mem_some_iff.mp present
    subst finished
    exact ⟨session,accepted,mismatched⟩

/-- The complete original pin-filtered public decision loses only the physical record mass and the same full warm source Exposure game. The successful session remains inside the event witness. -/
theorem bound (bounded : ∀publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (kind : Kind) :
    Pr{let result←job}[Pinned setup route source serverKeyId budget target kind result]≤
      Pr{let result←job}[PhysicalBad route source budget kind result]+Pr{let flag←wordGame}[flag=true] := by
  calc
    _≤Pr{let result←job}[PhysicalBad route source budget kind result ∨Mismatch source budget target result] := by
      apply prEvent_mono_of_support
      intro result supported pinned
      exact outcome setup checks route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper reservePackets bounds mode adversary budget target previous bounded result supported kind pinned
    _≤Pr{let result←job}[PhysicalBad route source budget kind result]+Pr{let result←job}[Mismatch source budget target result] :=
      prEvent_or_le _ _ _
    _≤_:=add_le_add le_rfl (mismatch_bound setup checks route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper reservePackets bounds mode adversary budget target previous)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound.outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound.outcome

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound.mismatch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound.mismatch_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound.bound
