-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged
/-! A Bundle callback appends only its own actual source stages to the existing canonical log. The same supported augmented packet retains this exact suffix through Fresh generation, every publication failure, and missing or inactive branches. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage recorded)
section Generic
variable {n :Nat} {KemSK R P Q S X :Type} {spec :OracleSpec Q}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform] [ed :AdapterInitEdPrimitive.Operations]
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

def Suffix (prior after :Events):Prop:=∃middle :List Stage,after=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage

theorem recorded_query (implementation :QueryImpl spec (StateT S (StateT P ProbComp)))
    (observation :(query :spec.Domain)→spec.Range query→List Stage) (prior :Events) (query :spec.Domain)
    (before :S×Events) (previous :P) (held :Suffix prior before.2)
    (result :(spec.Range query×(S×Events))×P)
    (supported :result∈support (((recorded implementation (fun query reply=>(observation query reply).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage) query).run before).run previous)) :
    Suffix prior result.1.2.2 :=by
  change result∈support (((fun inner=>(inner.1,(inner.2,before.2++(observation query inner.1).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))) <$>
    (implementation query).run before.1).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,same⟩:=supported
  cases same
  obtain ⟨leading,old⟩:=held
  refine ⟨leading++observation query inner.1.1,?_⟩
  change before.2++(observation query inner.1.1).map _=_
  rw [old,List.map_append,List.append_assoc]

theorem recorded_program (implementation :QueryImpl spec (StateT S (StateT P ProbComp)))
    (observation :(query :spec.Domain)→spec.Range query→List Stage) (prior :Events)
    (work :OracleComp spec X) (before :S×Events) (previous :P) (held :Suffix prior before.2)
    (result :(X×(S×Events))×P)
    (supported :result∈support (((simulateQ (recorded implementation
      (fun query reply=>(observation query reply).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)) work).run before).run previous)) :
    Suffix prior result.1.2.2 :=
  RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program _ (fun current=>Suffix prior current.2)
    (recorded_query implementation observation prior) work before previous held result supported

variable {I E :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner mlSource)

theorem runner (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (prior :Events)
    (result :((RegistrationNativePlatformExtractedSdkBundle.Publication×Native)×P)×Events)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBundleStageLog.runner coins setup checks representation created writer index owner
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage scalar before previous prior)) :Suffix prior result.2 :=by
  simp only [RegistrationNativePlatformPublicAdapterBundleStageLog.runner,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact recorded_program _ _ prior _ (before,prior) previous ⟨[],by simp only [List.map_nil,List.append_nil]⟩ inner called

theorem freshRunner (before :Native) (previous :P) (prior :Events)
    (result :(((PqxdhJointGapDh.ScalarBytes×RegistrationNativePlatformExtractedSdkBundle.Publication)×Native)×P)×Events)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner coins setup checks representation created writer index owner
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage before previous prior)) :Suffix prior result.2 :=by
  simp only [RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨sampled,_called,middle,continued,same⟩:=supported
  cases same
  exact runner coins setup checks representation created writer index owner sampled.1.1 sampled.1.2 sampled.2 prior middle continued
end Generic
section Configured
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT ProbComp)]
variable [originalCrypto :CryptoOperations (BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT ProbComp)]
variable [originalLocal :LocalOperations (BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical children other recording packedLocal packedCrypto)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "CutM"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)
local notation "previousLocal"=>RegistrationNativePlatformPublicAdapterLeaves.localOperations
  (S:=RegistrationNativePlatformCutJournal.State Native) originalLocal
noncomputable local instance idleLocal :LocalOperations (BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedLocal
noncomputable local instance idleCrypto :CryptoOperations (BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedCrypto
noncomputable local instance idleChildren :ChildOperations (BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=children

variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable {Log :Type}

open RegistrationNativePlatformPublicAdapterBundleLogged (step augmentation withCoinsAugmentation freshAugmentation)
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

def OnlyStages {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :TotalStep (Private configuration created credential) target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Events) (prior :Events) :Prop :=
  ∀result,result∈support augmented.sample→Suffix prior result.2

omit [FrameDispatchFallback.Operations] in
private theorem transport {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (left right :TotalStep (Private configuration created credential) target) (same :left=right)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation right Events) (prior :Events) :
    OnlyStages configuration created credential left (same.symm ▸augmented) prior ↔OnlyStages configuration created credential right augmented prior :=by
  cases same
  rfl

omit [FrameDispatchFallback.Operations] in
private theorem quiet {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :TotalStep (Private configuration created credential) target) (prior :Events) :
    OnlyStages configuration created credential call (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior) prior :=by
  intro result supported
  simp only [RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged,support_map] at supported
  obtain ⟨packet,_called,same⟩:=supported
  cases same
  exact ⟨[],by simp only [List.map_nil,List.append_nil]⟩

omit [FrameDispatchFallback.Operations] in
theorem stages (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) (prior :Events) :
    OnlyStages configuration created credential (step configuration created credential index before previous objects)
      (augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior) prior :=by
  cases selected:before.1.beacons[index]? with
  | none=>
    have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
        RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
      unfold augmentation
      exact (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
        ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans (by rfl))
    rw [augEq]
    exact quiet configuration created credential _ prior
  | some owner=>
    have found:=objects.base.beacons index
    rw [selected] at found
    let self:=Classical.choose found
    have sourceSelected :objects.base.objects.beacons index=some self:=(Classical.choose_spec found).1
    have related :AdapterPublicWrapperState.Beacon configuration.view setup.joint before.1.pool self owner
        before.1.server.world.world.1.owners[owner.worldOwner]? :=(Classical.choose_spec found).2
    cases stored:self.state with
    | Fresh control prekey kem=>
      have phase :owner.phase=.fresh :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        rfl
      let active:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
            stored phase before previous objects sourceSelected selected
      let activeAug:=freshAugmentation configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior
      have callEq :step configuration created credential index before previous objects=active :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=callEq.symm ▸activeAug :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq]
      apply (transport configuration created credential _ _ callEq activeAug prior).2
      intro result supported
      exact freshRunner coins setup checks configuration.agreement.representation created writer index owner before.1 previous prior result supported
    | FreshWithCoins control prekey oneTime kem=>
      have hasScalar :∃scalar,owner.phase=.freshWithCoins scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose hasScalar
      have phase :owner.phase=.freshWithCoins scalar:=Classical.choose_spec hasScalar
      let active:=RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected
      let activeAug:=withCoinsAugmentation configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior
      have callEq :step configuration created credential index before previous objects=active :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=callEq.symm ▸activeAug :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq]
      apply (transport configuration created credential _ _ callEq activeAug prior).2
      intro result supported
      exact runner coins setup checks configuration.agreement.representation created writer index owner scalar before.1 previous prior result supported
    | InitSent pending prekey oneTime kem=>
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq]
      exact quiet configuration created credential _ prior
    | Established control binding manager=>
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq]
      exact quiet configuration created credential _ prior
    | Aborted control=>
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ control stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq]
      exact quiet configuration created credential _ prior

omit [FrameDispatchFallback.Operations] in
theorem suffix (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) (prior :Events)
    (result :(step configuration created credential index before previous objects).step.Packet×Events)
    (supported :result∈support (augmentation configuration created credential index before previous objects
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior).sample) :
    ∃middle :List Stage,result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=
  stages configuration created credential index before previous objects prior result supported
end Configured
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.recorded_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.recorded_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.recorded_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.recorded_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.runner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.runner
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.freshRunner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.freshRunner
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.stages
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix.suffix
