-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionLocal
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual first-record/publication prefix yields its control/binding snapshot and material frame in the same run, including every failure. The joint conversion retains the complete external poststate and does not select a separate supported execution. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace
open BeaconcryptCore.Computational
open RegistrationNativePlatformSourceSealTrace (joint)
variable {n : Nat} {E Platform A B I KemSK Reader Response : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]

omit primitive in
private theorem joint_pure {S : Type} (value : A) :
    joint (pure value : StateT S (StateT Platform ProbComp) A) = pure value := by
  funext before
  simp only [joint, StateT.run_pure, map_pure]
  rfl

omit primitive in
private theorem joint_bind {S : Type} (work : StateT S (StateT Platform ProbComp) A)
    (next : A → StateT S (StateT Platform ProbComp) B) :
    joint (work >>= next) = (joint work >>= fun value => joint (next value)) := by
  funext before
  simp only [joint, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]

omit primitive in
private theorem joint_hom {S : Type} :
    Cslib.IsMonadHom (StateT S (StateT Platform ProbComp)) (StateT (S × Platform) ProbComp) joint :=
  .mk' joint_pure joint_bind

theorem joint_prefix (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) :
    joint (AdapterPublicServerCompletionLocal.beforeInstall (n := n) coins setup codec view failure allocation helper erased sign writer initial) =
      RegistrationServerSourceCompletionReceipt.program
        (fun query => joint (RegistrationNativePlatformServerCompletion.records coins setup codec query))
        (fun request => joint (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request))
        (fun transcript => joint (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript))
        (fun request => joint (RegistrationNativePlatformSourceBuild.write helper request))
        (fun query => joint (RegistrationNativePlatformServerCompletion.outgoing coins sign query))
        (fun value => joint (RegistrationNativePlatformSourceBuild.encode writer value)) initial := by
  unfold AdapterPublicServerCompletionLocal.beforeInstall RegistrationServerSourceCompletionReceipt.program
  rw [joint_bind, RegistrationNativePlatformSourceRecord.fromInitialWithHash_map joint_hom]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => exact joint_pure _
  | ok result => cases result with
    | Err rejected => exact joint_pure _
    | Ok pending => exact RegistrationNativePlatformBuildInterpret.Publication.program joint_hom _ _ pending

theorem post (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf)
    (before after : RegistrationServerRootCompiler.Local n) (previous next : Platform)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (supported : ((published, after), next) ∈ support
      (((AdapterPublicServerCompletionLocal.beforeInstall coins setup codec view failure allocation helper erased sign writer initial).run before).run previous)) :
    RegistrationServerSourceCompletionReceipt.Post initial published := by
  have reached : (published, (after, next)) ∈ support
      ((joint (AdapterPublicServerCompletionLocal.beforeInstall coins setup codec view failure allocation helper erased sign writer initial)).run (before, previous)) := by
    simp only [joint, StateT.run, support_map]
    exact ⟨((published, after), next), supported, rfl⟩
  rw [joint_prefix] at reached
  exact RegistrationServerSourceCompletionReceipt.stateful _ _ _ _ _ _ initial published (before, previous) (after, next) reached
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

theorem source_receipt (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK mlSource (StateT Platform ProbComp) RegistrationSigningShared.SignReply)
    (initial : registration.ServerInitialKdf)
    (sourceView : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (self : beaconcrypt_public_wrapper.server.Server)
    (before after : RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource))
    (related : AdapterPublicWrapperState.Server sourceView views created credential self before.1.server)
    (previous next : Platform) (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (supported : ((published, after), next) ∈ support
      (((AdapterPublicServerCompletionSource.beforeInstall
        (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) A) => AdapterPublicServerCompletionNative.inCut work)
        (AdapterPublicServerCompletionNative.outgoing coins sign) fallback coins setup codec view failure allocation helper erased
        (AdapterPublicServerCompletionNative.writer writer) initial).run before).run previous)) :
    RegistrationServerSourceCompletionReceipt.Post initial published ∧
      AdapterPublicWrapperState.Server sourceView views created credential self after.1.server := by
  have projectionEq := AdapterPublicServerCompletionNative.erasure coins setup codec view failure allocation helper erased sign writer fallback initial before
  have nativeSupport : ((published, after.1), next) ∈ support
      (((AdapterPublicServerCompletionNative.beforeInstall coins setup codec view failure allocation helper erased sign writer initial).run before.1).run previous) := by
    rw [← projectionEq]
    simp only [StateT.run_map, support_map]
    exact ⟨((published, after), next), supported, rfl⟩
  rw [AdapterPublicServerCompletionLocal.native_local, AdapterPublicServerLocalLens.local_run,
    StateT.run_map, support_map] at nativeSupport
  obtain ⟨⟨⟨actual, localAfter⟩, final⟩, called, same⟩ := nativeSupport
  have outputEq : actual = published := congrArg (fun result => result.1.1) same
  have stateEq : AdapterPublicServerLocalLens.putLocal before.1 localAfter = after.1 := congrArg (fun result => result.1.2) same
  have finalEq : final = next := congrArg Prod.snd same
  cases outputEq
  cases finalEq
  constructor
  · exact post coins setup codec view failure allocation helper erased sign writer initial before.1.server.world localAfter previous next published called
  · rw [← stateEq]
    exact AdapterPublicServerCompletionFrame.record_publication_material coins setup codec view failure allocation erased helper sign writer initial
      sourceView views created credential self before.1.server related previous (published, localAfter) next called

end BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace.joint_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace.joint_prefix
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace.post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace.post

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace.source_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionTrace.source_receipt
