-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared
import BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation
/-! The same recorded Bundle leaf preserves the complete earlier ML receipt prefix through actual hashing, Ed signing and writer failures. The retired Beacon ML-sign fallback returns None without a source signing operation or receipt. Persistent platform state and every failure reply stay in the same execution. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (recorded)
open RegistrationNativePlatformPublicAdapterSourceSigningHistory (receipts)
open RegistrationNativePlatformPublicAdapterSourceAuthentication (stages)
variable {n :Nat} {I KemSK E P R A :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P
local notation "Base"=>StateT P ProbComp
abbrev Spec (E :Type):=RegistrationNativePlatformWriter.Spec E

variable (coins :QueryImpl unifSpec (StateT P ProbComp)) (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner mlSource)

def history (before :Native):=before.server.world.world.2

def Aligned (before :Native×Events):Prop:=history before.1=receipts (stages before.2)

omit material platform ed in
theorem outgoing (query :RegistrationBeaconInitExecutor.Spec.Domain) (before :Native) (previous :P)
    (result :(RegistrationBeaconInitExecutor.Spec.Range query×Native)×P)
    (supported :result∈support (((RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner query).run before).run previous)) :
    history result.1.2=history before++receipts (RegistrationNativePlatformPublicAdapterBundleStageLog.observation (E:=E) (.inl query) result.1.1) :=by
  unfold RegistrationNativeBundleInterpretation.outgoing at supported
  rw [RegistrationNativeBundleInterpretation.legacy] at supported
  have actual:=RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 supported
  have law:=RegistrationNativeMldsaShared.source_program setup checks representation created index owner
    (RegistrationBeaconInitExecutor.Spec.query query) before
  simp only [simulateQ_spec_query] at law
  have projected :(result.1.1,RegistrationNativeMldsaShared.nativeProject result.1.2)∈support
      ((RegistrationNativeMldsaShared.implementation setup owner query).run (RegistrationNativeMldsaShared.nativeProject before)) :=by
    rw [←law,support_map]
    exact ⟨result.1,actual,rfl⟩
  cases query with
  | inl query=>cases query with
    | hash request=>
      simp only [RegistrationNativeMldsaShared.implementation,RegistrationSigningShared.implementation,
        MldsaSharedNative.authentication,StateT.run,support_map] at projected
      obtain ⟨inner,_called,same⟩:=projected
      have sameHistory:=congrArg (fun value=>value.2.1) same
      simpa only [history,RegistrationNativeMldsaShared.nativeProject,RegistrationNativePlatformPublicAdapterBundleStageLog.observation,
        RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation,receipts,List.filterMap_cons,List.filterMap_nil,
        RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipt,List.append_nil] using sameHistory.symm
    | sign request payload digest=>
      simp only [RegistrationNativeMldsaShared.implementation,StateT.run_pure,support_pure,Set.mem_singleton_iff] at projected
      have sameHistory:=congrArg (fun value=>value.2.1) projected
      simpa only [history,RegistrationNativeMldsaShared.nativeProject,RegistrationNativePlatformPublicAdapterBundleStageLog.observation,
        receipts,List.filterMap_nil,List.append_nil] using sameHistory
  | inr request=>
    simp only [RegistrationNativeMldsaShared.implementation,StateT.run_pure,support_pure,Set.mem_singleton_iff] at projected
    have sameHistory:=congrArg (fun value=>value.2.1) projected
    simpa only [history,RegistrationNativeMldsaShared.nativeProject,RegistrationNativePlatformPublicAdapterBundleStageLog.observation,
      receipts,List.filterMap_nil,List.append_nil] using sameHistory

theorem append_log (before :Events) (fresh :List RegistrationNativePlatformPublicAdapterSourceTrace.Stage) :
    receipts (stages (before++fresh.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))=
      receipts (stages before)++receipts fresh :=by
  simp only [stages,List.filterMap_append,List.filterMap_map,Function.comp_def,List.filterMap_some,
    receipts,List.filterMap_append]

theorem query (query :(Spec E).Domain) (before :Native×Events) (previous :P) (aligned :Aligned before)
    (result :((Spec E).Range query×(Native×Events))×P)
    (supported :result∈support (((recorded
      (RegistrationNativePlatformPublicAdapterBundleStageLog.native coins setup checks representation created writer index owner)
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBundleStageLog.observation query reply).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage) query).run before).run previous)) :
    Aligned result.1.2 :=by
  change result∈support (((fun inner=>(inner.1,(inner.2,before.2++
    (RegistrationNativePlatformPublicAdapterBundleStageLog.observation query inner.1).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage))) <$>
      (RegistrationNativePlatformPublicAdapterBundleStageLog.native coins setup checks representation created writer index owner query).run before.1).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  cases query with
  | inl query=>
    have delta:=outgoing coins setup checks representation created writer index owner query before.1 previous inner called
    unfold Aligned
    rw [append_log,delta,aligned]
  | inr query=>
    simp only [RegistrationNativePlatformPublicAdapterBundleStageLog.native,StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at called
    obtain ⟨response,_possible,same⟩:=called
    cases same
    simpa only [Aligned,RegistrationNativePlatformPublicAdapterBundleStageLog.observation,List.map_nil,List.append_nil] using aligned

omit material platform ed in
theorem persistent_program {Q S X :Type} {spec :OracleSpec Q}
    (implementation :QueryImpl spec (StateT S (StateT P ProbComp))) (invariant :S→Prop)
    (keeps :∀query before previous, invariant before→∀result,
      result∈support (((implementation query).run before).run previous)→invariant result.1.2)
    (work :OracleComp spec X) (before :S) (previous :P) (held :invariant before)
    (result :(X×S)×P) (supported :result∈support (((simulateQ implementation work).run before).run previous)) :
    invariant result.1.2 :=by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact held
  | query_bind request next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,following⟩:=supported
    exact ih middle.1.1 middle.1.2 middle.2 (keeps request before previous held middle called) result following

theorem program (work :OracleComp (Spec E) A) (before :Native×Events) (previous :P) (aligned :Aligned before)
    (result :(A×(Native×Events))×P)
    (supported :result∈support (((simulateQ (recorded
      (RegistrationNativePlatformPublicAdapterBundleStageLog.native coins setup checks representation created writer index owner)
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBundleStageLog.observation query reply).map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)) work).run before).run previous)) :
    Aligned result.1.2 :=by
  exact persistent_program _ Aligned (query coins setup checks representation created writer index owner) work before previous aligned result supported

theorem runner (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (prior :Events)
    (aligned :Aligned (before,prior))
    (result :((RegistrationNativePlatformExtractedSdkBundle.Publication×Native)×P)×Events)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBundleStageLog.runner coins setup checks representation created writer index owner
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage scalar before previous prior)) :
    history result.1.1.2=receipts (stages result.2) :=by
  simp only [RegistrationNativePlatformPublicAdapterBundleStageLog.runner,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  cases same
  exact program coins setup checks representation created writer index owner _ (before,prior) previous aligned inner called


omit material platform ed in
private theorem sample_no_sign (work :ProbComp A) :
    RegistrationNativeMldsaNoSign.Holds
      (RegistrationNativeBeaconFrontend.sample (n:=n) (KemSK:=KemSK) (mldsaSource:=mlSource) (Auxiliary:=RegistrationServerRoleBackend.State) work) :=by
  let implementation :QueryImpl unifSpec (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) :=
    fun query=>(RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl (.inl query))
  have first :simulateQ (fun query=>StateT.lift (implementation query)) work=
      (StateT.lift (simulateQ implementation work) :StateT (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) A) :=
    simulateQ_liftTarget implementation work
  have second :simulateQ (fun query=>StateT.lift (StateT.lift (implementation query))) work=
      (StateT.lift (simulateQ (fun query=>StateT.lift (implementation query)) work) :RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State A) :=
    simulateQ_liftTarget (n:=RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State)
      (fun query=>(StateT.lift (implementation query) :StateT (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
        (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) (unifSpec.Range query))) work
  change RegistrationNativeMldsaNoSign.Holds (simulateQ (fun query=>StateT.lift (StateT.lift (implementation query))) work)
  rw [second,first]
  intro owners env result supported
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,Functor.map_map,support_map] at supported
  obtain ⟨inner,_possible,same⟩:=supported
  cases same
  rfl

omit material platform ed in
theorem sample (before :Native) (previous :P) (result :(PqxdhJointGapDh.ScalarBytes×Native)×P)
    (supported :result∈support (((RegistrationNativeBundleLifetime.sample coins setup checks representation created writer).run before).run previous)) :
    history result.1.2=history before :=by
  unfold RegistrationNativeBundleLifetime.sample at supported
  rw [RegistrationNativeBundleInterpretation.legacy] at supported
  have actual:=RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 supported
  exact RegistrationNativeMldsaReceiptPreservation.beacon setup checks representation created _ (sample_no_sign PqxdhJointGapDh.sampleScalar) before result.1 actual

theorem freshRunner (before :Native) (previous :P) (prior :Events) (aligned :Aligned (before,prior))
    (result :(((PqxdhJointGapDh.ScalarBytes×RegistrationNativePlatformExtractedSdkBundle.Publication)×Native)×P)×Events)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner coins setup checks representation created writer index owner
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage before previous prior)) :
    history result.1.1.2=receipts (stages result.2) :=by
  simp only [RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨sampled,called,middle,continued,same⟩:=supported
  cases same
  have kept:=sample coins setup checks representation created writer before previous sampled called
  have nextAligned :Aligned (sampled.1.2,prior) :=kept.trans aligned
  exact runner coins setup checks representation created writer index owner sampled.1.1 sampled.1.2 sampled.2 prior nextAligned middle continued

omit material platform ed in
theorem lifecycle (scalar :PqxdhJointGapDh.ScalarBytes) (published :RegistrationNativePlatformExtractedSdkBundle.Publication) (before :Native) :
    history (RegistrationNativeBundleLifecycle.after index owner scalar published before)=history before :=by
  cases published with
  | fail error | div=>rfl
  | ok result=>cases result <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.append_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.append_log
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.runner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.runner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.sample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.freshRunner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.freshRunner
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.lifecycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.lifecycle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta.persistent_program
