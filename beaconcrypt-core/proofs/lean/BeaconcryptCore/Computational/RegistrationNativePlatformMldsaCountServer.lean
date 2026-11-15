-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk
import BeaconcryptCore.Computational.RegistrationNativePlatformPinView
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer

/-! Actual source Server publication retains its complete optional signer replies, stateful source response writer and shared platform poststate under explicit private count normalization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer
open BeaconcryptCore.Refinement
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformMldsaCountRules (Correct)
open RegistrationNativeMldsaCountServer (localProject signingProject serverProject)
variable {n : Nat} {Auxiliary Platform E : Type} {source : RegistrationNativeMldsa.Source}
variable (credential : RegistrationNativeMldsa.Credential source)

private theorem local_idempotent (before : RegistrationWorldAgreement.State n Auxiliary) :
    localProject (localProject before) = localProject before := by
  simp only [localProject, RegistrationNativeMldsaWorldView.idempotent]

private theorem local_outgoing (query : RegistrationSigningShared.Spec.Domain) :
    RegistrationNativeMldsaCountRules.Correct (localProject (n := n) (Auxiliary := Auxiliary))
      (fun before => (fun result => (result.1, { before with world := result.2 })) <$>
        (RegistrationNativeMldsaServer.outgoing source credential query).run before.world) := by
  constructor
  · intro before
    have same := congrArg (fun action => (fun result => (result.1,
      { localProject before with world := result.2 })) <$> action)
      ((RegistrationNativeMldsaCountServer.outgoing source credential query).1 before.world)
    simp only [StateT.run, Functor.map_map, Prod.map, id_eq, localProject, signingProject] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun action => (fun result => (result.1,
      { localProject before with world := result.2 })) <$> action)
      ((RegistrationNativeMldsaCountServer.outgoing source credential query).2 before.world)
    simp only [StateT.run, RegistrationNativeMldsaCountMap.transform, simulateQ_map,
      Functor.map_map, Prod.map, id_eq, localProject, signingProject] at same ⊢
    exact same

/-- Every actual response hash/sign leaf satisfies both free count laws while retaining all source operands and optional replies. -/
theorem outgoing (query : RegistrationSigningShared.Spec.Domain) :
    Correct (source := source) (Platform := Platform) (localProject (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformMldsaServer.outgoing source credential query) :=
  RegistrationNativePlatformMldsaCountRules.inject localProject _ (local_outgoing credential query)

namespace Publication
open RegistrationNativePlatformServerPublication
private theorem continue_correct {Input : Type} (action : RustM Input)
    (next : Input → StateT (RegistrationWorldAgreement.State n Auxiliary) (M source Platform)
      (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))))
    (law : ∀ input, Correct localProject (next input)) : Correct localProject (continueWith action next) := by
  cases action with
  | ok input => exact law input
  | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _

private theorem result {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT (RegistrationWorldAgreement.State n Auxiliary) (M source Platform)
      (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))))
    (law : ∀ input, Correct localProject (next input)) : Correct localProject (continueResult action next) := by
  cases action with
  | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
    | Ok input => exact law input

private theorem ready
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseReady) :
    Correct (source := source) (Platform := Platform) (localProject (n := n) (Auxiliary := RegistrationServerRoleBackend.State))
      (RegistrationNativePlatformServerPublication.ready
        (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformSourceBuild.encode writer view)) pending) := by
  unfold RegistrationNativePlatformServerPublication.ready
  apply continue_correct
  intro view
  apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _
    (RegistrationNativePlatformMldsaCountRules.external localProject local_idempotent _)
  intro _encoded
  exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _

private theorem signing
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.ServerResponseSigning) :
    Correct (source := source) (Platform := Platform) (localProject (n := n) (Auxiliary := RegistrationServerRoleBackend.State))
      (RegistrationNativePlatformServerPublication.signing (RegistrationNativePlatformMldsaServer.outgoing source credential)
        (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformSourceBuild.encode writer view)) payload digest pending) := by
  unfold RegistrationNativePlatformServerPublication.signing
  apply continue_correct
  intro request
  apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _ (outgoing credential (.sign request payload digest))
  intro reply
  exact result _ _ (fun selected => ready writer selected)

private theorem program
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseHash) :
    Correct (source := source) (Platform := Platform) (localProject (n := n) (Auxiliary := RegistrationServerRoleBackend.State))
      (RegistrationNativePlatformServerPublication.program (RegistrationNativePlatformMldsaServer.outgoing source credential)
        (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformSourceBuild.encode writer view)) pending) := by
  unfold RegistrationNativePlatformServerPublication.program
  apply continue_correct
  intro request
  apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _ (outgoing credential (.hash request))
  intro digest
  exact result _ _ (fun selected => signing credential writer _ digest selected)
end Publication

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

private theorem lift_pure {S V : Type} (value : V) :
    RegistrationNativePlatformMldsaProgram.lift (source := source)
      (pure value : StateT S (StateT Platform ProbComp) V) = pure value := by
  funext before previous
  rfl
private theorem lift_bind {S V W : Type}
    (work : StateT S (StateT Platform ProbComp) V)
    (next : V → StateT S (StateT Platform ProbComp) W) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (work >>= next) =
      (RegistrationNativePlatformMldsaProgram.lift work >>= fun value => RegistrationNativePlatformMldsaProgram.lift (next value)) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    StateT.run_bind, RegistrationNativeMldsaProgram.lift, simulateQ_bind]
  rfl

private theorem capability_stable (query : PqxdhRecordLiftInterface.Capability n) :
    RegistrationNativeKemCounterIndependence.Stable (localProject (Auxiliary := Auxiliary))
      (RegistrationWorldServerCompletion.capability query) := by
  intro before
  have same := congrArg (fun computation => (fun result => (result.1,
    { localProject before with world := (result.2, before.world.2) })) <$> computation)
    (RegistrationNativeMldsaWorldView.effects (.inr query) before.world.1)
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, Functor.map_map,
    Prod.map, id_eq, localProject] at same ⊢
  exact same

private theorem capability (query : PqxdhRecordLiftInterface.Capability n) :
    Correct (source := source) (Platform := Platform) (localProject (Auxiliary := Auxiliary))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins query)) :=
  RegistrationNativePlatformMldsaCountRules.native localProject _ (capability_stable query)

private theorem install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) :
    Correct (source := source) (Platform := Platform) (localProject (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformServerCompletion.installWith
          (RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins) control published)) := by
  unfold RegistrationNativePlatformServerCompletion.installWith
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerCompletion.continueResult, lift_pure]
    exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
  | ok answer => cases answer with
    | Err prior =>
      simp only [RegistrationNativePlatformServerCompletion.continueResult, lift_pure]
      exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
    | Ok pending =>
      simp only [RegistrationNativePlatformServerCompletion.continueResult]
      cases request : pending.request with
      | fail error | div =>
        simp only [RegistrationNativePlatformServerCompletion.continueWith, lift_pure]
        exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
      | ok keyId =>
        simp only [RegistrationNativePlatformServerCompletion.continueWith]
        cases parts : pending.into_parts with
        | fail error | div =>
          simp only [lift_pure]
          exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
        | ok parts =>
          simp only [lift_bind, lift_pure]
          exact RegistrationNativePlatformMldsaCountRules.bind localProject _ _ (capability _)
            (fun _ => RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _)

/-- The actual response publication, source writer and peer install continuation preserve both count laws on all outcomes. -/
theorem afterRecord
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    Correct (source := source) (localProject (n := n) (Auxiliary := RegistrationServerRoleBackend.State))
      (RegistrationNativePlatformMldsaServer.afterRecord source credential writer control hashed) := by
  unfold RegistrationNativePlatformMldsaServer.afterRecord
  apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _ (Publication.program credential writer hashed)
  intro published
  cases published with
  | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
    | Ok ready => exact install control ready


private theorem lift_world {V : Type}
    (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) V) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (RegistrationNativePlatformServerSdk.world work) =
      RegistrationNativePlatformServerSdk.world (RegistrationNativePlatformMldsaProgram.lift work) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativePlatformServerSdk.world, StateT.run, map_apply,
    RegistrationNativeMldsaProgram.lift, simulateQ_map]

private theorem present (keyId : U64) :
    Correct (source := source) (serverProject (n := n))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformCompletionSdk.nativePresent (m := StateT Platform ProbComp) RegistrationNativePlatformMldsaProgram.coins keyId)) := by
  rw [RegistrationNativePlatformCompletionSdk.nativePresent, lift_world]
  exact RegistrationNativePlatformMldsaCountSdk.world _ (capability (.peerPresent keyId))

private theorem local_adHash (pending : registration.ServerAdHash) :
    Correct (source := source) (Platform := Platform) (localProject (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformServerCompletion.adHash RegistrationNativePlatformMldsaProgram.coins pending)) := by
  unfold RegistrationNativePlatformServerCompletion.adHash RegistrationNativePlatformServerCompletion.adHashWith
    RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div =>
    rw [lift_pure]
    exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
  | ok request =>
    simp only [bind_assoc,pure_bind,lift_bind,lift_pure]
    apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _ (capability _)
    intro digest
    exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _

/-- The actual transcript hash retains both source count equations and its complete reached state. -/
theorem adHash (pending : registration.ServerAdHash) :
    Correct (source := source) (Platform := Platform) (serverProject (n := n))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformCompletionSdk.nativeAdHash (m := StateT Platform ProbComp) RegistrationNativePlatformMldsaProgram.coins pending)) := by
  rw [RegistrationNativePlatformCompletionSdk.nativeAdHash,RegistrationNativePlatformServerSdk.adHash,lift_world]
  exact RegistrationNativePlatformMldsaCountSdk.world _ (local_adHash pending)


open PqxdhServerAuthExperiment (Setup Codec)
variable {ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]

/-- The actual first-record source allocator, AEAD, mutable hash and raw writer compose with publication on every count-normalized failure branch. -/
theorem finish (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Correct localProject (RegistrationNativePlatformMldsaServer.finish (n := n) source credential setup codec view failure allocation erased helper writer control initial) := by
  unfold RegistrationNativePlatformMldsaServer.finish
  apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _
    (RegistrationNativePlatformMldsaCountRules.closed localProject _
      (RegistrationNativePlatformSourceRecordView.record RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation erased helper initial))
  intro recorded
  cases recorded with
  | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaCountRules.pure localProject local_idempotent _
    | Ok hashed => exact afterRecord credential writer control hashed

/-- Literal current source build has both count equations, with its real AD-hash effect and complete native/platform poststates. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    Correct serverProject (RegistrationNativePlatformMldsaServer.build (n := n) source credential setup codec view failure allocation erased reservePeer helper writer handle application) := by
  unfold RegistrationNativePlatformMldsaServer.build
  exact RegistrationNativePlatformMldsaCountSdk.build
    (fun pending => RegistrationNativePlatformMldsaProgram.lift
      (RegistrationNativePlatformCompletionSdk.nativeAdHash RegistrationNativePlatformMldsaProgram.coins pending)) adHash _
    (RegistrationNativePlatformMldsaCountRules.closed serverProject _
      (RegistrationNativePlatformPinView.pin RegistrationNativePlatformMldsaProgram.coins)) _
    (RegistrationNativePlatformMldsaCountRules.external serverProject
      (fun before => by simp only [serverProject, local_idempotent]) reservePeer) _ present _
    (finish credential setup codec view failure allocation erased helper writer) handle application

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.afterRecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.afterRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.adHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer.adHash
