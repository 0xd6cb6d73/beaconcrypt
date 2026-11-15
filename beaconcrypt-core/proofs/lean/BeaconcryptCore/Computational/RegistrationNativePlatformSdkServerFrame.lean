-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleLifetime
import BeaconcryptCore.Computational.RegistrationNativeFinishLifetime
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
/-! Actual source primitive and bundle publication callbacks preserve the Server object coordinates and opaque token table. The complete auxiliary and primitive states still change and remain retained by the execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame
open RegistrationNativeBeaconFrontend (Trusted Owner)
variable {n : Nat} {I KemSK A Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

structure ServerImage where
  control : pqxdh.ServerState
  pin : session.ServerAuthenticationPin
  consumed : RegistrationReplaySchedule.State
  sessions : List (Option peer.ConsumedRegistration)
  records : Option PqxdhRecordLiftWorld.Server

def image (state : Native) : ServerImage :=
  ⟨state.server.control,state.server.pin,state.server.consumed,state.server.sessions,state.server.world.world.1.server⟩

private theorem sampled_server (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n)
    (result : A ×PqxdhRecordLiftWorld.State n)
    (reached : result∈support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    result.2.server=before.server := by
  simp only [PqxdhRecordLiftWorld.sampled,StateT.run,bind_pure_comp,support_map] at reached
  obtain ⟨inner,_called,same⟩ := reached
  cases same
  rfl

theorem trusted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (Trusted n KemSK).Domain) (safe : RegistrationNativeWorldOwnerFrame.Safe (KemSK := KemSK) query)
    (before : Native) (result : (Trusted n KemSK).Range query ×Native)
    (reached : result∈support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    image result.2=image before := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeExperiment.trusted,RegistrationNativeExperiment.world,
        RegistrationNativeExperiment.server,StateT.run,Functor.map_map,support_map] at reached
      obtain ⟨inner,called,same⟩ := reached
      cases same
      have records : inner.2.server=before.server.world.world.1.server := by
        cases query with
        | inl coin => exact sampled_server _ (PqxdhRecordLiftWorld.chargeEffect (.inl coin) _) inner called
        | inr capability => cases capability with
          | hash bytes =>
              simp only [PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,StateT.run,mem_support_bind_iff] at called
              obtain ⟨middle,sampled,returned⟩ := called
              simp only [support_pure,Set.mem_singleton_iff] at returned
              cases returned
              exact sampled_server _ (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) _) middle sampled
          | _ => exact False.elim safe
      exact congrArg (fun server =>(⟨before.server.control,before.server.pin,before.server.consumed,before.server.sessions,server⟩ : ServerImage)) records
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted,StateT.run,mem_support_bind_iff] at reached
      obtain ⟨inner,called,returned⟩ := reached
      simp only [support_pure,Set.mem_singleton_iff] at returned
      cases returned
      exact congrArg (fun server =>(⟨before.server.control,before.server.pin,before.server.consumed,before.server.sessions,server⟩ : ServerImage))
        (sampled_server _ _ inner called)

theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Trusted n KemSK) A)
    (allowed : AllQueriesSatisfy work (RegistrationNativeWorldOwnerFrame.Safe (KemSK := KemSK)))
    (before : Native) (result : A ×Native)
    (reached : result∈support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    image result.2=image before := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at reached
      cases reached
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at reached
      obtain ⟨inner,called,continued⟩ := reached
      exact (ih inner.1 (allowed.2 inner.1) inner.2 result continued).trans
        (trusted setup checks representation created query allowed.1 before inner called)

variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem bundle_query (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain)
    (allowed : RegistrationNativeBundleSafety.Allowed (E := E) (n := n) (KemSK := KemSK) query)
    (before : Native) (previous : Platform)
    (result : ((RegistrationNativePlatformGenericBundle.Spec E n KemSK).Range query ×Native) ×Platform)
    (reached : result∈support (((RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer query).run before).run previous)) :
    image result.1.2=image before := by
  cases query with
  | inl query =>
      have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 reached
      apply trusted setup checks representation created query _ before result.1 actual
      cases query with
      | inl effect => cases effect with
        | inl coin => trivial
        | inr capability => cases capability <;> trivial
      | inr query => exact False.elim allowed
  | inr query =>
      simp only [RegistrationNativePlatformExperiment.bundleHandler,RegistrationNativePlatformExperiment.writer,
        StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at reached
      obtain ⟨inner,_called,same⟩ := reached
      cases same
      rfl

theorem bundle_program (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) A)
    (allowed : work.AllQueriesSatisfy (RegistrationNativeBundleSafety.Allowed (E := E) (n := n) (KemSK := KemSK)))
    (before : Native) (previous : Platform) (result : (A ×Native) ×Platform)
    (reached : result∈support (((simulateQ (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before).run previous)) :
    image result.1.2=image before := by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at reached
      cases reached
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at reached
      obtain ⟨inner,called,continued⟩ := reached
      exact (ih inner.1.1 (allowed.2 inner.1.1) inner.1.2 inner.2 result continued).trans
        (bundle_query coins setup checks representation created writer query allowed.1 before previous inner called)

theorem bundle_interpreted (work : RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State
      (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK)) A)
    (allowed : RegistrationNativePlatformFrontend.Work
      (RegistrationNativeBundleSafety.Allowed (E := E) (n := n) (KemSK := KemSK)) work)
    (before : Native) (previous : Platform) (result : (A ×Native) ×Platform)
    (reached : result∈support (((RegistrationNativePlatformFrontend.interpret
      (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before).run previous)) :
    image result.1.2=image before := by
  rw [RegistrationNativePlatformFrontend.run_interpret,StateT.run_map,support_map] at reached
  obtain ⟨inner,called,same⟩ := reached
  cases same
  exact bundle_program coins setup checks representation created writer _
    (allowed before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world)) before previous inner called

theorem bundle_tree (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Native) (previous : Platform)
    (result : (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) ×Native) ×Platform)
    (reached : result∈support (((RegistrationNativeBundleLifetime.tree coins setup checks representation created writer index owner scalar).run before).run previous)) :
    image result.1.2=image before :=
  bundle_interpreted coins setup checks representation created writer _
    (RegistrationNativeBundleSafety.publication_safe setup index owner scalar) before previous result reached

theorem beacon (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (allowed : RegistrationNativeBeaconPrefixSafe.Work work) (before : Native) (result : A ×Native)
    (reached : result∈support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    image result.2=image before := by
  simp only [RegistrationNativeExperiment.beacon,StateT.run,mem_support_bind_iff] at reached
  obtain ⟨inner,called,returned⟩ := reached
  simp only [support_pure,Set.mem_singleton_iff] at returned
  cases returned
  exact program setup checks representation created _
    (allowed before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world)) before inner called

theorem bundle_sample (before : Native) (previous : Platform)
    (result : (PqxdhJointGapDh.ScalarBytes ×Native) ×Platform)
    (reached : result∈support (((RegistrationNativeBundleLifetime.sample coins setup checks representation created writer).run before).run previous)) :
    image result.1.2=image before := by
  unfold RegistrationNativeBundleLifetime.sample at reached
  rw [RegistrationNativeBundleInterpretation.legacy] at reached
  have called := RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 reached
  exact beacon setup checks representation created _
    (RegistrationNativeBeaconPrefixSafe.sample_safe PqxdhJointGapDh.sampleScalar) before result.1 called

theorem bundle_fresh_tree (index : Nat) (owner : Owner source) (before : Native) (previous : Platform)
    (result : ((PqxdhJointGapDh.ScalarBytes ×RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) ×Native) ×Platform)
    (reached : result∈support (((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer index owner).run before).run previous)) :
    image result.1.2=image before := by
  simp only [RegistrationNativeBundleLifetime.fresh_tree,StateT.run_bind,bind_pure_comp,StateT.run_map,mem_support_bind_iff] at reached
  obtain ⟨drawn,sampled,continued⟩ := reached
  rw [support_map] at continued
  obtain ⟨published,called,same⟩ := continued
  cases same
  exact (bundle_tree coins setup checks representation created writer index owner drawn.1.1 drawn.1.2 drawn.2 published called).trans
    (bundle_sample coins setup checks representation created writer before previous drawn sampled)

theorem bundle_after (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (before : Native) :
    image (RegistrationNativeBundleLifecycle.after index owner scalar reply before)=image before := by
  cases reply with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

theorem finish_after (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted)
    (reply : RustM (Option registration.CompletedBeacon)) (owners : List (Owner source))
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Native) :
    image (RegistrationNativeFinishTerminalTree.after index owner control reply
      (RegistrationNativeFinishTerminalTree.assemble owners environment before))=image before := by
  cases reply with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

theorem finish_tree (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending)
    (packet : Option registration.ResponsePacket) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Native)
    (result : (RustM (Option registration.CompletedBeacon) ×RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×Native)
    (reached : result∈support (RegistrationNativeFinishLifetime.tree setup checks representation created wire pending packet owner scalar before)) :
    image result.2=image before := by
  exact program setup checks representation created _
    (RegistrationNativeFinishBodySafety.raw_safe setup wire pending _ owner scalar _)
    before result reached

variable [material : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [ed : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
theorem server_material (view : BeaconcryptCore.Refinement.AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : BeaconcryptCore.Refinement.AdapterPublicWrapperStorage.Views)
    (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before after : Native)
    (related : BeaconcryptCore.Refinement.AdapterPublicWrapperState.Server view containers created credential self before.server)
    (same : image after=image before) :
    BeaconcryptCore.Refinement.AdapterPublicWrapperState.Server view containers created credential self after.server := by
  have control := congrArg ServerImage.control same
  have pin := congrArg ServerImage.pin same
  have consumed := congrArg ServerImage.consumed same
  have records := congrArg ServerImage.records same
  refine {related with control := related.control.trans control.symm, pinIdentity := ?_, pinIdentifier := ?_, pinMldsa := ?_, replay := ?_, peers := ?_}
  · rw [show after.server.pin=before.server.pin from pin]
    exact related.pinIdentity
  · rw [show after.server.pin=before.server.pin from pin]
    exact related.pinIdentifier
  · rw [show after.server.pin=before.server.pin from pin]
    exact related.pinMldsa
  · rw [show after.server.consumed=before.server.consumed from consumed]
    exact related.replay
  · change ∃entry,after.server.world.world.1.server=some entry ∧_
    rw [show after.server.world.world.1.server=before.server.world.world.1.server from records]
    exact related.peers

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.trusted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_interpreted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_tree
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_sample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_fresh_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_fresh_tree
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.bundle_after
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.finish_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.finish_after
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.finish_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.finish_tree
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.server_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame.server_material
