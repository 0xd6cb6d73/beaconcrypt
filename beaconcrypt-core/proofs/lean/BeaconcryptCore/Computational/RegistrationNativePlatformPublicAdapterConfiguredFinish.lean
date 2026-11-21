-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
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
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical children packedLocal packedCrypto raw_cast)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
noncomputable local instance idleLocal :LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedLocal
noncomputable local instance idleCrypto :CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedCrypto
noncomputable local instance idleChildren :ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=children
local instance idleCodecs :Codecs (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=AdapterPublicConcreteCodecs.codecs
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)

noncomputable def typed (current :Native×P) (before :Private configuration created credential current) (index :Nat) (input :Slice U8) :=
  RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks configuration.agreement.representation created wire
    configuration.view configuration.views credential current.1 index input current.2 before

noncomputable def step (current :Native×P) (before :Private configuration created credential current) (index :Nat) (input :Slice U8) :
    TotalStep (Private configuration created credential) ((model configuration created credential (.inr (.finish index input))).run current) :=by
  let call:=RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
    (typed configuration created credential current before index input)
  refine RegistrationNativePlatformPublicAdapterBuildRaw.modelCast ?_ call
  change _=RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential
      (.inr (.finish index (TranscriptAuthParts.absSlice input)))).run current.1).run current.2)
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native
  rw [RegistrationNativePlatformPublicAdapterRawModel.finish]
  simp only [StateT.run_map,Functor.map_map]
  rfl

omit originalGenerators originalCrypto originalLocal originalContainers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] primitives in
private theorem raw_map {N Reply PublicReply :Type} {Private :N→Type} {target :ProbComp (Reply×N)}
    (call :TotalStep Private target) (physical :∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (observe :Reply→PublicReply) :
    raw physical (RegistrationNativePlatformPublicAdapterReply.map observe call)=
      (Prod.map (Functor.map (Prod.map observe id)) id) <$>raw physical call :=by
  unfold raw
  conv_rhs=>erw [Functor.map_map]
  rfl

noncomputable def sourceCall (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) (index :Nat) (input :Slice U8) :=
  (Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id) <$>
    RegistrationNativePlatformSdkFinishPhysical.source (mlSource:=source) coins setup checks configuration.agreement.representation created configuration.erased
      configuration.parseEd configuration.verifyEd writer before index input

theorem query (current :Native×P) (before :Private configuration created credential current) (index :Nat) (input :Slice U8) :
    raw (physical configuration created credential) (step configuration created credential current before index input)=
      sourceCall configuration created (physical configuration created credential current before) index input :=by
  unfold step
  rw [raw_cast]
  exact (raw_map _ _ RegistrationNativeRawAdapter.resultOption).trans
    (congrArg (fun tree=>(Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id) <$>tree)
      (RegistrationNativePlatformSdkFinishPhysical.query coins setup checks configuration.agreement.representation created wire configuration.erased
        configuration.parseEd configuration.verifyEd writer configuration.initial configuration.view
        (RegistrationNativePlatformPublicAdapterConfiguration.common configuration) configuration.decapsulation configuration.views credential
        current.1 index input current.2 before))

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish.query
