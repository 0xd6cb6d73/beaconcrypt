-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! Initialized execution uses actual returned source objects, RNG and sampled physical World. Its event transport consumes the internally discharged concrete dispatcher source law, retaining returned values, the full secrecy ledger and persistent platform state. This base runtime is the erasure marginal of the separately instrumented source operation log. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution
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
variable (decision :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R→Bool)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical

noncomputable def work (publication :RegistrationNativeExperiment.Public) :=
  RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto codec publication.serverKeyId bounds mode (adversary publication)

def observe (output :RustM ((Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R)×
    (RegistrationNativePlatformSdkReification.Backend n KemSK×P)) :Bool×P :=
  (match output.1 with | .ok (value,objects)=>decision (value,objects) | .fail _ | .div=>false,output.2.2)

noncomputable def profile :StateT P ProbComp Bool :=fun previous=>do
  let packet←RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng
  match packet.val.1.ready with
  | none=>pure (false,previous)
  | some ready=> observe decision <$>
    (RegistrationNativePlatformPublicAdapterSourceRuntime.run
      (simulateQ (RegistrationNativePlatformPublicAdapterDispatcher.interpreter configuration ready.initial.created)
        (work (setup:=setup) bounds mode adversary ready.initial.public))
      (RegistrationNativePlatformPublicAdapterInitializationPhysical.initialStore packet.val.2 ready previous))

noncomputable def commonProfile :StateT P ProbComp Bool :=fun previous=>do
  let packet←RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng
  match returned:packet.val.1.ready with
  | none=>pure (false,previous)
  | some ready=>
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit
      serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready returned
    (fun result=>(decision (result.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects
      (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration ready.initial.created ready.initial.credential result.2.1 result.2.2)),result.2.1.1.2)) <$>
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler
        (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration ready.initial.created ready.initial.credential))
        (work (setup:=setup) bounds mode adversary ready.initial.public)).run
        ⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩

omit [PublicWrapperPlatform.CryptoOperations] [AdapterServerConstructorPrimitive.Standard] [FrameDispatchFallback.Operations] in
theorem external (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (stored :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential before) :
    (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration created credential before stored).backend.2=before.1.2 :=
  congrArg Prod.snd stored.base.backend

omit [PublicWrapperPlatform.CryptoOperations] [AdapterServerConstructorPrimitive.Standard] [FrameDispatchFallback.Operations] in
theorem cache (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (stored :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential before) :
    (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration created credential before stored).backend.1.world.primitive.2=
      RegistrationNativeWorldCache.cache before.1.1 :=
  congrArg (fun current=>current.1.world.primitive.2) stored.base.backend

include objects serverEd in
theorem common_source :
    commonProfile (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary decision=
      profile (n:=n) configuration identityIndex identifier rng bounds mode adversary decision :=by
  funext previous
  unfold commonProfile profile
  apply bind_congr
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>rfl
  | some ready=>
    dsimp only
    let packet :{value //value∈support (RegistrationNativePlatformPublicAdapterInitializationPhysical.raw (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng)}:=⟨(⟨constructor,some ready⟩,world),supported⟩
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit serverEd
      configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready rfl
    let start :RegistrationNativePlatformExtractedSdkPublic.State
      (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration ready.initial.created ready.initial.credential):=
      ⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩
    have initial:=RegistrationNativePlatformPublicAdapterInitializationPhysical.physical setup configuration.generator configuration.view configuration.views objects ensureInit serverEd
      configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready rfl
    change RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration ready.initial.created ready.initial.credential start.1 start.2=
      RegistrationNativePlatformPublicAdapterInitializationPhysical.initialStore world ready previous at initial
    have physical:=RegistrationNativePlatformPublicAdapterDispatcher.program configuration ready.initial.created ready.initial.credential
      (work (setup:=setup) bounds mode adversary ready.initial.public) start
    have observed:=congrArg (fun computation=>observe decision <$>computation) physical
    rw [Functor.map_map] at observed
    rw [initial] at observed
    refine Eq.trans ?_ observed
    apply congrArg (fun observation=>observation <$>
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler
        (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration ready.initial.created ready.initial.credential))
        (work (setup:=setup) bounds mode adversary ready.initial.public)).run start)
    funext result
    change (decision (result.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects
      (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration ready.initial.created ready.initial.credential result.2.1 result.2.2)),result.2.1.1.2)=
      (decision (result.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects
      (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration ready.initial.created ready.initial.credential result.2.1 result.2.2)),(RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration ready.initial.created ready.initial.credential result.2.1 result.2.2).backend.2)
    rw [external]


omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] originalGenerators originalCrypto [AdapterServerConstructorPrimitive.Standard] in
private theorem bind_apply {S A B :Type} (action :StateT S ProbComp A) (next :A→StateT S ProbComp B) (before :S) :
    (action >>=next) before=(do let result←action before;next result.1 result.2) :=rfl
omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] originalGenerators originalCrypto [AdapterServerConstructorPrimitive.Standard] in
private theorem lift_apply {S A :Type} (action :ProbComp A) (before :S) :
    (StateT.lift action :StateT S ProbComp A) before=(fun value=>(value,before)) <$>action :=bind_pure_comp _ _
omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] originalGenerators originalCrypto [AdapterServerConstructorPrimitive.Standard] in
private theorem map_apply {S A B :Type} (f :A→B) (action :StateT S ProbComp A) (before :S) :
    (f <$>action) before=Prod.map f id <$>action before :=StateT.run_map f action before

variable (nativeDecision :RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)→Bool)

noncomputable def nativeProfile :StateT P ProbComp Bool :=
  RegistrationNativePlatformExtractedExperiment.profile setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
    configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
    (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) bounds mode
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) nativeDecision

include objects serverEd in
theorem common_native
    (event_source :∀(created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
      (current :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
      (stored :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential current)
      (valueLedger :Value×RegistrationNativeLedger.State),
      decision (valueLedger,RegistrationNativePlatformPublicAdapterSourceRuntime.objects
        (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration created credential current stored))=
        nativeDecision (valueLedger.1,(valueLedger.2,current.1.1))) :
    commonProfile (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary decision=
      nativeProfile configuration ensureInit identityIndex identifier bounds mode adversary nativeDecision :=by
  funext previous
  have initialized:=RegistrationNativePlatformPublicAdapterInitializationPhysical.native (n:=n) setup configuration.generator configuration.view
    configuration.views objects ensureInit serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng
  unfold commonProfile nativeProfile RegistrationNativePlatformExtractedExperiment.profile
  simp only [bind_apply,lift_apply,bind_map_left]
  rw [←initialized,bind_map_left]
  apply bind_congr
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>rfl
  | some ready=>
    dsimp only [AdapterServerConstructorRunner.nativeView,Option.map_some]
    let packet :{value //value∈support (RegistrationNativePlatformPublicAdapterInitializationPhysical.raw (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng)}:=⟨(⟨constructor,some ready⟩,world),supported⟩
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit serverEd
      configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready rfl
    let start :RegistrationNativePlatformExtractedSdkPublic.State
      (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration ready.initial.created ready.initial.credential):=
      ⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩
    have public_run:=RegistrationNativePlatformExtractedSdkPublic.program
      (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration ready.initial.created ready.initial.credential)
      (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration ready.initial.created ready.initial.credential)
      (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration ready.initial.created ready.initial.credential)
      (work (setup:=setup) bounds mode adversary ready.initial.public) start
    have erased:=congrArg (fun computation=>Prod.map id Prod.fst <$>computation) public_run
    have compiled:=RegistrationNativePlatformPublicAdapterFullProgram.program configuration ready.initial.created ready.initial.credential
      ready.initial.public.serverKeyId bounds mode (adversary ready.initial.public) start.1
    have erased_run :
        (fun result=>(result.1,result.2.1.1)) <$>
          (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler
            (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration ready.initial.created ready.initial.credential)
            (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration ready.initial.created ready.initial.credential)
            (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration ready.initial.created ready.initial.credential))
            (work (setup:=setup) bounds mode adversary ready.initial.public)).run start=
        (RegistrationNativePlatformPackedState.pack
          (RegistrationNativePlatformExtractedExperiment.run setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
            configuration.agreement.representation ready.initial.created source ready.initial.credential configuration.keyView configuration.sealFailure
            (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
            configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
            (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
            (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) bounds mode
            (RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary ready.initial.public)))).run (ready.initial.state,previous) :=by
      convert erased.trans compiled using 1
      · simp only [Functor.map_map,RegistrationNativePlatformExtractedSdkPublic.project,Prod.map_def,id_eq]
      · rfl
    have observed:=congrArg (fun computation=>(fun result=>(nativeDecision (result.1.1,(result.1.2,result.2.1)),result.2.2)) <$>computation) erased_run
    dsimp only [RegistrationNativePlatformPackedState.pack,StateT.run] at observed
    simp only [Functor.map_map] at observed
    simp only [map_apply]
    refine Eq.trans ?_ observed
    apply congrArg (fun observation=>observation <$>
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler
        (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration ready.initial.created ready.initial.credential))
        (work (setup:=setup) bounds mode adversary ready.initial.public)).run start)
    funext result
    exact congrArg (fun value=>(value,result.2.1.1.2))
      (event_source ready.initial.created ready.initial.credential result.2.1 result.2.2 result.1)

include objects serverEd in
theorem profile_source
    (event_source :∀(created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
      (current :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
      (stored :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential current)
      (valueLedger :Value×RegistrationNativeLedger.State),
      decision (valueLedger,RegistrationNativePlatformPublicAdapterSourceRuntime.objects
        (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration created credential current stored))=
        nativeDecision (valueLedger.1,(valueLedger.2,current.1.1))) :
    profile (n:=n) configuration identityIndex identifier rng bounds mode adversary decision=
      nativeProfile configuration ensureInit identityIndex identifier bounds mode adversary nativeDecision :=
  (common_source configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary decision).symm.trans
    (common_native configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary decision nativeDecision event_source)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.external' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.external
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.cache
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.common_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.common_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.common_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.common_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.profile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution.profile_source
