-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterFinishLogSuffix (Suffix)
section Sample
variable {n :Nat} {I KemSK P Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource

theorem sample (coins :QueryImpl unifSpec (StateT P ProbComp))
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)
    (wire :RegistrationNativeWire.Wire) (note :Stage→Log)
    (pending :registration.BeaconPending) (input :Slice U8) (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (previous :P) (past :List Log)
    (reached :(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×List Log)
    (supported :reached∈support (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
      pending (AdapterPublicFinishLifetime.packet input) owner scalar before previous past)) :Suffix note past reached.2 :=by
  have logged:(RegistrationNativePlatformPublicAdapterFinishSampleStageCut.result reached)∈support
      (RegistrationNativePlatformPublicAdapterFinishStageCut.logged
        (RegistrationNativePlatformPublicAdapterFinishSampleStageCut.implementation coins setup checks representation created)
        (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body setup wire note pending
          (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar)
        (RegistrationWorldAgreementCompiler.erase before.server.world) past (before,previous)) :=by
    rw [←RegistrationNativePlatformPublicAdapterFinishSampleStageCut.sample_source coins setup checks representation created wire note pending input owner scalar before previous past,support_map]
    exact ⟨reached,supported,rfl⟩
  exact RegistrationNativePlatformPublicAdapterFinishLogSuffix.body
    (RegistrationNativePlatformPublicAdapterFinishSampleStageCut.implementation coins setup checks representation created) setup wire note pending
    (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world) past (before,previous)
    (RegistrationNativePlatformPublicAdapterFinishSampleStageCut.result reached) logged
end Sample
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformSdkReification (Backend)
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

local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
open RegistrationNativePlatformExtractedSdkPublic (returned returned_exact store)
open RegistrationNativePlatformSdkReification (backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private physical)

open RegistrationNativePlatformPublicAdapterLoggedRuntime (Augmentation unchanged)
open RegistrationNativePlatformPublicAdapterFinishLoggedJoint (output physicalLog)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential mlSource)

open RegistrationNativePlatformPublicAdapterFinishLoggedDispatch (augmentation transport)

omit [FrameDispatchFallback.Operations] [PublicWrapperPlatform.CryptoOperations] in
private theorem transport_suffix {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    {left right :TotalStep (Private configuration created credential) target}
    (same :left=right) (augmented :Augmentation left (List Log)) (note :Stage→Log) (past :List Log)
    (law :∀result,result∈support augmented.sample→Suffix note past result.2)
    (result :right.step.Packet×List Log)
    (supported :result∈support (transport configuration created credential same augmented).sample) :Suffix note past result.2 :=by
  cases same
  exact law result supported

omit [FrameDispatchFallback.Operations] in
theorem configured (current :Native×P) (objects :Private configuration created credential current)
    (index :Nat) (input :Slice U8) (note :Stage→Log) (past :List Log)
    (result :(RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input).step.Packet×List Log)
    (supported :result∈support (augmentation configuration created credential current objects index input note past).sample) :Suffix note past result.2 :=by
  cases selected:current.1.beacons[index]? with
  | none=>
    have augEq:augmentation configuration created credential current objects index input note past=
      unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
      unfold augmentation
      exact (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
        ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans (by rfl))
    rw [augEq] at supported
    exact Or.inl (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log _ past ⟨result,supported⟩)
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected :objects.base.objects.beacons index=some self:=(Classical.choose_spec prior).1
    have related :AdapterPublicWrapperState.Beacon configuration.view setup.joint current.1.pool self owner
      current.1.server.world.world.1.owners[owner.worldOwner]? :=(Classical.choose_spec prior).2
    cases stored:self.state with
    | InitSent pending prekey oneTime kem=>
      have phase :∃scalar,owner.phase=.initSent pending scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        cases matched.1
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose phase
      have phase:owner.phase=.initSent pending scalar:=Classical.choose_spec phase
      have callEq:RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input=
          RegistrationNativePlatformSdkFinishCoupled.active coins setup checks configuration.agreement.representation created wire
            configuration.view configuration.views credential self pending prekey oneTime kem stored input owner scalar current.1 index selected phase current.2 objects sourceSelected :=by
        unfold RegistrationNativePlatformPublicAdapterConfiguredFinish.typed RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq:augmentation configuration created credential current objects index input note past=
          transport configuration created credential callEq.symm
            (RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active configuration created credential self pending prekey oneTime kem stored input owner scalar
              current.1 index selected phase current.2 objects sourceSelected note past) :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq] at supported
      apply transport_suffix configuration created credential callEq.symm _ note past _ result supported
      intro reached called
      exact sample coins setup checks configuration.agreement.representation created wire note pending input owner scalar current.1 current.2 past reached called
    | Fresh control prekey kem=>
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq] at supported
      exact Or.inl (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log _ past ⟨result,supported⟩)
    | FreshWithCoins control prekey oneTime kem=>
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq] at supported
      exact Or.inl (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log _ past ⟨result,supported⟩)
    | Established control binding manager=>
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq] at supported
      exact Or.inl (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log _ past ⟨result,supported⟩)
    | Aborted control=>
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ control stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq] at supported
      exact Or.inl (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log _ past ⟨result,supported⟩)

omit [FrameDispatchFallback.Operations] in
theorem suffix (current :Native×P) (objects :Private configuration created credential current)
    (index :Nat) (input :Slice U8) (past :RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P)
    (result :(RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input).step.Packet×RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P)
    (supported :result∈support (augmentation configuration created credential current objects index input RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage past).sample) :
    ∃middle :List Stage,result.2=past++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  rcases configured configuration created credential current objects index input RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage past result supported with same|⟨initial,reply,same⟩
  · exact ⟨[],by simpa only [List.map_nil,List.append_nil] using same⟩
  · exact ⟨[.beaconFirstRecord initial reply],same⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory.sample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory.configured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory.configured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory.suffix
