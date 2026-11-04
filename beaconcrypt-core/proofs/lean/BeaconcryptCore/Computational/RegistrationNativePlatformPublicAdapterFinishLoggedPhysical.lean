-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
/-! The Finish source observation executes the actual source agreement and first-record controller once. It records the genuine beacon initializer and actual first-record reply before any later installation, retains arbitrary earlier observations, and erases to the literal source SDK body. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK P E R Error Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
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
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=mlSource) setup checks)
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)

noncomputable def body (created :PqxdhLiveServerConstruction.Created Unit) (note :Stage→Log)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8)
    (before :Backend n KemSK × (P × List Log)) :
    ProbComp ((RustM AdapterPublicFinishBody.Result ×Backend n KemSK)×(P×List Log)) :=
  letI :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformSdkFinishSampling.uniformP coins) originalCrypto
  (fun result=>((result.1.1.1,result.1.2),(result.2,result.1.1.2))) <$>
    (((RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.run (mlSource:=mlSource) setup RegistrationNativeConcreteCodec.wire
      (RegistrationNativePlatformSdkFinishPhysicalBody.trusted coins setup checks configuration.agreement.representation created) note
      configuration.erased (fun input=>StateT.lift (configuration.parseEd input)) (fun input key=>StateT.lift (configuration.verifyEd input key))
      (fun query=>StateT.lift (writer query)) self input).run before.2.2).run before.1).run before.2.1

def dropStore (before :Store n KemSK R (P×List Log)) :Store n KemSK R P :=
  {before with backend:=(before.backend.1,before.backend.2.1)}

def dropRaw (result :RustM (Option Pqxdh.Bytes×Store n KemSK R (P×List Log))×(Backend n KemSK×(P×List Log))) :
    RustM (Option Pqxdh.Bytes×Store n KemSK R P)×(Backend n KemSK×P) :=
  (Prod.map id dropStore <$>result.1,(result.2.1,result.2.2.1))

omit [FrameDispatchFallback.Operations] in
theorem body_erase (created :PqxdhLiveServerConstruction.Created Unit) (note :Stage→Log)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8)
    (before :Backend n KemSK × (P × List Log)) :
    (fun result=>((result.1.1,result.1.2),result.2.1)) <$>body configuration created note self input before=
      ((RegistrationNativePlatformSdkFinishPhysicalBody.body (n:=n) (source:=mlSource) coins setup checks
        configuration.agreement.representation created configuration.erased configuration.parseEd configuration.verifyEd writer self input).run before.1).run before.2.1 :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformSdkFinishSampling.uniformP coins) originalCrypto
  have erased:=RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program_erase (m:=PhysicalM) setup RegistrationNativeConcreteCodec.wire
    (RegistrationNativePlatformSdkFinishPhysicalBody.trusted coins setup checks configuration.agreement.representation created) note
    configuration.view (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup configuration.view
      (RegistrationNativePlatformPublicAdapterConfiguration.common configuration)) self input before.2.2
  have observed:=congrArg (fun action=>(action.run before.1).run before.2.1) erased
  have actual:=RegistrationNativePlatformSdkFinishPhysicalBody.body_source (P:=P) (n:=n) coins setup checks configuration.agreement.representation created
    configuration.erased configuration.parseEd configuration.verifyEd writer configuration.initial configuration.view
    (RegistrationNativePlatformPublicAdapterConfiguration.common configuration) self input
  have logged:=RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.source (m:=PhysicalM) setup RegistrationNativeConcreteCodec.wire
    (RegistrationNativePlatformSdkFinishPhysicalBody.trusted coins setup checks configuration.agreement.representation created) note
    configuration.view (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup configuration.view
      (RegistrationNativePlatformPublicAdapterConfiguration.common configuration)) configuration.erased
    (fun input=>StateT.lift (configuration.parseEd input)) (fun input key=>StateT.lift (configuration.verifyEd input key))
    (fun query=>StateT.lift (writer query)) self input
  rw [actual]
  simp only [body]
  rw [logged]
  simpa only [StateT.run_map,Functor.map_map] using observed

noncomputable def run (created :PqxdhLiveServerConstruction.Created Unit) (note :Stage→Log)
    (before :Store n KemSK R (P×List Log)) (index :Nat) (input :Slice U8) :
    ProbComp (RustM (Option Pqxdh.Bytes×Store n KemSK R (P×List Log))×(Backend n KemSK×(P×List Log))) :=
  match before.beacons index with
  | none=>pure (.ok (none,before),before.backend)
  | some self=>(Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id) <$>
      (RegistrationNativePlatformSdkFinishPhysical.finish before index <$>body configuration created note self input before.backend)

omit originalGenerators originalCrypto originalLocal originalContainers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] primitives in
private theorem finish_drop (before :Store n KemSK R (P×List Log)) (index :Nat)
    (reached :(RustM AdapterPublicFinishBody.Result×Backend n KemSK)×(P×List Log)) :
    dropRaw (Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id
      (RegistrationNativePlatformSdkFinishPhysical.finish before index reached))=
      Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id
        (RegistrationNativePlatformSdkFinishPhysical.finish (dropStore before) index ((reached.1.1,reached.1.2),reached.2.1)) :=by
  rcases reached with ⟨⟨reply,backend⟩,previous,log⟩
  cases reply <;> rfl

omit [FrameDispatchFallback.Operations] in
theorem erase (created :PqxdhLiveServerConstruction.Created Unit) (note :Stage→Log)
    (before :Store n KemSK R (P×List Log)) (index :Nat) (input :Slice U8) :
    dropRaw <$>run configuration created note before index input=
      RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall configuration created (dropStore before) index input :=by
  unfold run RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall RegistrationNativePlatformSdkFinishPhysical.source
  cases selected:before.beacons index with
  | none=>simp only [dropStore,selected,map_pure];rfl
  | some self=>
    simp only [dropStore,selected,Functor.map_map]
    have source:=body_erase configuration created note self input before.backend
    have observed:=congrArg (fun action=>(fun reached=>Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id
      (RegistrationNativePlatformSdkFinishPhysical.finish (dropStore before) index reached)) <$>action) source
    simp only [Functor.map_map] at observed
    refine Eq.trans ?_ observed
    congr 1
    funext reached
    exact finish_drop before index reached

noncomputable def operation (created :PqxdhLiveServerConstruction.Created Unit)
    (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) (index :Nat) (input :Slice U8) :
    ProbComp (RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P (Option Pqxdh.Bytes)) :=
  (Prod.map (Functor.map (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects)) id) <$>
    run configuration created RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage before index input

omit [FrameDispatchFallback.Operations] in
theorem operation_erase (created :PqxdhLiveServerConstruction.Created Unit)
    (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) (index :Nat) (input :Slice U8) :
    RegistrationNativePlatformPublicAdapterSourceEvents.outcome <$>operation configuration created before index input=
      (Prod.map (Functor.map (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects)) id) <$>
        RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall configuration created
          (RegistrationNativePlatformPublicAdapterSourceEvents.store before) index input :=by
  have law:=congrArg (fun action=>(Prod.map (Functor.map (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects)) id) <$>action)
    (erase configuration created RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage before index input)
  simp only [operation,Functor.map_map]
  simp only [Functor.map_map] at law
  refine Eq.trans ?_ law
  congr 1
  funext result
  rcases result with ⟨reply,backend⟩
  cases reply <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.body_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.body_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.operation_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.operation_erase
