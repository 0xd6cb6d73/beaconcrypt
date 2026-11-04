-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonPath
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing
/-! Every supported initialized common source result supplies its own full source path and genuine initial sampler receipt. The observed KEM history forgets only observations already projected by the checked marginal; this receipt retains the actual common execution's intermediate pools. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt
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


def history (initial :RegistrationNativeExperiment.Initial n KemSK source)
    (result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration initial.created initial.credential) :
    RegistrationNativePlatformKemInitializedJournal.History n source Value P:=
  ⟨RegistrationNativePlatformKemCountedProfile.ofInitial initial,result.1,
    RegistrationNativeKemServerState.ofNative result.2.1.1.1.1,
    result.2.1.1.2.calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativePlatformOrdinaryKemClientJournal.observe)⟩

include objects serverEd in
theorem receipt (previous :P) (initial :RegistrationNativeExperiment.Initial n KemSK source)
    (result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration initial.created initial.credential)
    (supported :(some ⟨initial,result⟩:RegistrationNativePlatformPublicAdapterKemHistory.Outcome (n:=n) configuration)∈support
      (RegistrationNativePlatformPublicAdapterKemHistory.sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous)) :
    Nonempty (RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
      configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
      (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
      configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
      (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
      (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) previous
      (history configuration initial result) result.2.1.1.1.2 result.2.1.1.1.1.pool) :=by
  unfold RegistrationNativePlatformPublicAdapterKemHistory.sample at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨packet,sampled,continued⟩:=supported
  split at continued
  next selected=>
    simp only [mem_support_pure_iff] at continued
    cases continued
  next ready selected=>
    rw [support_map] at continued
    obtain ⟨output,called,same⟩:=continued
    have pairEq:=Option.some.inj same
    cases pairEq
    have startup :some ready.initial∈support (RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex identifier):=by
      have initialized:=RegistrationNativePlatformPublicAdapterInitializationPhysical.native (n:=n) setup configuration.generator configuration.view
        configuration.views objects ensureInit serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng
      have member:AdapterServerConstructorRunner.nativeView packet.val.1∈support
          ((fun current=>AdapterServerConstructorRunner.nativeView current.val.1) <$>
            RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng):=by
        rw [support_map]
        exact ⟨packet,sampled,rfl⟩
      rw [initialized] at member
      simpa only [AdapterServerConstructorRunner.nativeView,selected,Option.map_some] using member
    have reached:=RegistrationNativePlatformPublicAdapterSourceCommonPath.program configuration ready.initial.created ready.initial.credential
      ready.initial.public.serverKeyId bounds mode (adversary ready.initial.public)
      (ready.initial.state,previous)
      (RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit
        serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready selected)
      [] output called
    exact ⟨⟨ready.initial,startup,output.2.1.1.2.calls,output.2.1.1.1.1,reached,rfl,rfl,rfl,rfl⟩⟩

include objects serverEd in
theorem exact_receipt (previous :P) (initial :RegistrationNativeExperiment.Initial n KemSK source)
    (result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration initial.created initial.credential)
    (supported :(some ⟨initial,result⟩:RegistrationNativePlatformPublicAdapterKemHistory.Outcome (n:=n) configuration)∈support
      (RegistrationNativePlatformPublicAdapterKemHistory.sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous)) :
    ∃execution :(RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
      configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
      (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
      configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
      (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
      (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) previous
      (history configuration initial result) result.2.1.1.1.2 result.2.1.1.1.1.pool), execution.initial=initial ∧execution.calls=result.2.1.1.2.calls ∧execution.finalNative=result.2.1.1.1.1 :=by
  unfold RegistrationNativePlatformPublicAdapterKemHistory.sample at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨packet,sampled,continued⟩:=supported
  split at continued
  next selected=>
    simp only [mem_support_pure_iff] at continued
    cases continued
  next ready selected=>
    rw [support_map] at continued
    obtain ⟨output,called,same⟩:=continued
    have pairEq:=Option.some.inj same
    cases pairEq
    have startup :some ready.initial∈support (RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex identifier):=by
      have initialized:=RegistrationNativePlatformPublicAdapterInitializationPhysical.native (n:=n) setup configuration.generator configuration.view
        configuration.views objects ensureInit serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng
      have member:AdapterServerConstructorRunner.nativeView packet.val.1∈support
          ((fun current=>AdapterServerConstructorRunner.nativeView current.val.1) <$>
            RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng):=by
        rw [support_map]
        exact ⟨packet,sampled,rfl⟩
      rw [initialized] at member
      simpa only [AdapterServerConstructorRunner.nativeView,selected,Option.map_some] using member
    have reached:=RegistrationNativePlatformPublicAdapterSourceCommonPath.program configuration ready.initial.created ready.initial.credential
      ready.initial.public.serverKeyId bounds mode (adversary ready.initial.public)
      (ready.initial.state,previous)
      (RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit
        serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready selected)
      [] output called
    exact ⟨⟨ready.initial,startup,output.2.1.1.2.calls,output.2.1.1.1.1,reached,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩

omit [AdapterServerConstructorPrimitive.Standard] in
theorem invariant_path (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    {before after :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential}
    {calls :List (RegistrationNativeStageTrace.Call RegistrationNativePlatformPublicAdapterLowSpec.Spec
      (RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential))}
    (path :RegistrationNativeStageTrace.Path (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential) before calls after)
    (held :RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration created credential before) :
    RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration created credential after :=by
  induction path with
  | nil=>exact held
  | cons call called rest last following ih=>
    exact ih (RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop.query configuration created credential
      call.query call.before held (call.reply,call.after) called)

include objects serverEd in
theorem source_path (previous :P) (initial :RegistrationNativeExperiment.Initial n KemSK source)
    (result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration initial.created initial.credential)
    (supported :(some ⟨initial,result⟩:RegistrationNativePlatformPublicAdapterKemHistory.Outcome (n:=n) configuration)∈support
      (RegistrationNativePlatformPublicAdapterKemHistory.sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous)) :
    ∃stored :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration initial.created initial.credential
        ((initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),
      ∃calls :List (RegistrationNativeStageTrace.Call RegistrationNativePlatformPublicAdapterLowSpec.Spec
        (RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration initial.created initial.credential)),
      RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration initial.created initial.credential
        (⟨((initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[]) ∧
      RegistrationNativeStageTrace.Path (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration initial.created initial.credential)
        (⟨((initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[]) calls result.2 :=by
  unfold RegistrationNativePlatformPublicAdapterKemHistory.sample at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨packet,sampled,continued⟩:=supported
  split at continued
  next selected=>
    simp only [mem_support_pure_iff] at continued
    cases continued
  next ready selected=>
    rw [support_map] at continued
    obtain ⟨output,called,same⟩:=continued
    have pairEq:=Option.some.inj same
    cases pairEq
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit
      serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready selected
    let start :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration ready.initial.created ready.initial.credential:=
      (⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[])
    have held:=RegistrationNativePlatformPublicAdapterAuthenticationSecurity.cold configuration previous identityIndex identifier rng packet ready selected stored
    obtain ⟨calls,path⟩:=RegistrationNativePlatformPublicAdapterSourceLogCrossing.path
      (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration ready.initial.created ready.initial.credential)
      (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public) start output called
    exact ⟨stored,calls,held,path⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.exact_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.exact_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.invariant_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.invariant_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.source_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt.source_path
