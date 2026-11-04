-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! Initialized execution uses actual returned source objects, RNG and sampled physical World. Its event transport consumes the internally discharged concrete dispatcher source law, retaining returned values, the full secrecy ledger and persistent platform state. The analysis sample retains the actual initialized source log and its same native history together; projection forgets only the source objects, stage log and extra authentication flag. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable [AdapterServerConstructorPrimitive.Standard]
variable {Value :Type}
variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (ensureInit :StateT Unit ProbComp Bool)
variable (serverEd :AdapterServerConstructorJoint.EdContract configuration.generator configuration.view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical

abbrev Outcome :=Option (Σinitial :RegistrationNativeExperiment.Initial n KemSK source,
  (Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration initial.created initial.credential)

noncomputable def sample (previous :P) :ProbComp (Outcome (n:=n) (Value:=Value) configuration) :=do
  let packet←RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng
  match returned:packet.val.1.ready with
  | none=>pure none
  | some ready=>
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit
      serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready returned
    (fun result=>some ⟨ready.initial,result⟩) <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public)).run
        (⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[])

noncomputable def observe (previous :P)
    (decision :RegistrationNativeExperiment.Public→(Value×RegistrationNativeLedger.State)→
      RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P→Bool) :
    Outcome (n:=n) (Value:=Value) configuration→Bool×P
  | none=>(false,previous)
  | some ⟨initial,result⟩=>RegistrationNativePlatformPublicAdapterExecution.observe decision initial.public
      (RegistrationNativePlatformPublicAdapterSourceRuntime.embed
        (result.1,RegistrationNativePlatformPublicAdapterLoggedJoint.sourceState configuration initial.created initial.credential result.2))

abbrev Observed :=((Option (RegistrationNativePlatformKemInitializedJournal.History n source Value P)×P)×PqxdhLiveKemBirth.Pool KemSK)

noncomputable def project (previous :P) :Outcome (n:=n) (Value:=Value) configuration→Observed (n:=n) (KemSK:=KemSK) (source:=source) (P:=P) (Value:=Value)
  | none=>((none,previous),PqxdhLiveKemBirth.empty)
  | some ⟨initial,result⟩=>
    ((some ⟨RegistrationNativePlatformKemCountedProfile.ofInitial initial,result.1,
      RegistrationNativeKemServerState.ofNative result.2.1.1.1.1,
      result.2.1.1.2.calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativePlatformOrdinaryKemClientJournal.observe)⟩,
      result.2.1.1.1.2),result.2.1.1.1.1.pool)

include objects serverEd in
theorem sample_observe (previous :P)
    (decision :RegistrationNativeExperiment.Public→(Value×RegistrationNativeLedger.State)→
      RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P→Bool) :
    observe configuration previous decision <$>
      sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous=
      (RegistrationNativePlatformPublicAdapterLoggedExecution.commonProfile (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng
        bounds mode adversary decision).run previous :=by
  unfold sample RegistrationNativePlatformPublicAdapterLoggedExecution.commonProfile
  rw [map_bind]
  apply bind_congr
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>simp only [map_pure];rfl
  | some ready=>simp only [Functor.map_map];rfl

include objects serverEd in
theorem source_profile (previous :P)
    (decision :RegistrationNativeExperiment.Public→(Value×RegistrationNativeLedger.State)→
      RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P→Bool) :
    observe configuration previous decision <$>
      sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous=
      (RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary decision).run previous :=
  (sample_observe configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous decision).trans
    (congrArg (fun action=>action.run previous)
      (RegistrationNativePlatformPublicAdapterLoggedExecution.common_source configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary decision))

include objects serverEd in
theorem native (previous :P) :
    project (n:=n) configuration previous <$>
      sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous=
    RegistrationNativePlatformOrdinaryKemHistorySource.native (n:=n) setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
      configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
      (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
      configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
      (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
      (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) bounds mode
      (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous :=by
  have initialized:=RegistrationNativePlatformPublicAdapterInitializationPhysical.native (n:=n) setup configuration.generator configuration.view
    configuration.views objects ensureInit serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng
  unfold sample RegistrationNativePlatformOrdinaryKemHistorySource.native
  rw [map_bind,←initialized,bind_map_left]
  apply bind_congr
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>simp only [map_pure];rfl
  | some ready=>
    dsimp only [AdapterServerConstructorRunner.nativeView,Option.map_some]
    let packet :{value //value∈support (RegistrationNativePlatformPublicAdapterInitializationPhysical.raw (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng)}:=⟨(⟨constructor,some ready⟩,world),supported⟩
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit serverEd
      configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready rfl
    let start :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration ready.initial.created ready.initial.credential:=
      (⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[])
    have joint:=RegistrationNativePlatformPublicAdapterKemHistoryProgram.program configuration ready.initial.created ready.initial.credential
      ready.initial.public.serverKeyId bounds mode (adversary ready.initial.public) start
    let observeNative (result :(Value×RegistrationNativeLedger.State)×((RegistrationNativeExperiment.State n KemSK source×P)×
        List (RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeKemServerState.State n source×P)))) :
        Observed (n:=n) (KemSK:=KemSK) (source:=source) (P:=P) (Value:=Value):=
      ((some ⟨RegistrationNativePlatformKemCountedProfile.ofInitial ready.initial,result.1,
        RegistrationNativeKemServerState.ofNative result.2.1.1,result.2.2⟩,result.2.1.2),result.2.1.1.pool)
    have observed:=congrArg (fun computation=>observeNative <$>computation) joint
    simp only [Functor.map_map] at observed
    simp only [bind_pure_comp,Functor.map_map] at ⊢
    exact observed

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory.sample_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory.sample_observe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory.source_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory.source_profile
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory.native
