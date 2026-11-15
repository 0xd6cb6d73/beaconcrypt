-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublicationCached
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache

/-! Actual source Server completion preserves cached ML signing receipts through real first-record allocation, mutable hashing, raw writing, signature attempts and peer installation. Every SDK prefix and failed outcome is retained, and every structural premise is discharged from the actual source body. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerCached
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformSdkCached (Keeps localProject serverProject)
variable {n : Nat} {E Platform Value Next State ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem pure_keeps (projection : State → RegistrationSigningShared.State) (value : Value) :
    Keeps (Platform := Platform) projection (pure value) := by
  intro before previous result valid supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact valid

private theorem bind_keeps (projection : State → RegistrationSigningShared.State)
    (work : StateT State (StateT Platform ProbComp) Value) (next : Value → StateT State (StateT Platform ProbComp) Next)
    (first : Keeps projection work) (rest : ∀ value, Keeps projection (next value)) : Keeps projection (work >>= next) := by
  intro before previous result valid supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first before previous middle valid called) continued

private theorem frame_keeps (projection : State → RegistrationSigningShared.State)
    (work : StateT State (StateT Platform ProbComp) Value)
    (frame : ∀ before previous result, result ∈ support ((work.run before).run previous) →
      (projection result.1.2).1 = (projection before).1 ∧ (projection before).2 ≤ (projection result.1.2).2) : Keeps projection work := by
  intro before previous result valid supported
  obtain ⟨receipts, extension⟩ := frame before previous result supported
  change RegistrationSigningShared.Cached ((projection result.1.2).1, (projection result.1.2).2)
  rw [receipts]
  exact RegistrationSigningShared.cached_extend _ _ _ extension valid

private theorem capability (query : PqxdhRecordLiftInterface.Capability n) :
    Keeps (Platform := Platform) localProject (RegistrationNativePlatformServerCompletion.capability coins query) := by
  apply frame_keeps
  intro before previous result supported
  have actual : result.1 ∈ support ((RegistrationWorldServerCompletion.capability query).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
  obtain ⟨inner, called, same⟩ := actual
  have historyEq : result.1.2.world.2 = before.world.2 := (congrArg (fun value => value.2.world.2) same).symm
  have cacheEq := congrArg (fun value => value.2.world.1.primitive.2) same
  refine ⟨historyEq, ?_⟩
  change before.world.1.primitive.2 ≤ result.1.2.world.1.primitive.2
  rw [← cacheEq]
  exact RegistrationWorldCache.effects_cache (.inr query) before.world.1 inner called

private theorem install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) :
    Keeps (Platform := Platform) (localProject (n := n))
      (RegistrationNativePlatformServerCompletion.installWith (RegistrationNativePlatformServerCompletion.capability coins) control published) := by
  unfold RegistrationNativePlatformServerCompletion.installWith
  cases moved : peer.begin_peer_insert control published with
  | fail error | div => exact pure_keeps localProject _
  | ok answer => cases answer with
    | Err previous => exact pure_keeps localProject _
    | Ok pending =>
      dsimp only [RegistrationNativePlatformServerCompletion.continueResult]
      cases requested : pending.request with
      | fail error | div => exact pure_keeps localProject _
      | ok keyId =>
        dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
        cases unpacked : pending.into_parts with
        | fail error | div => exact pure_keeps localProject _
        | ok parts =>
          dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
          exact bind_keeps localProject _ _ (capability _) (fun _ => pure_keeps localProject _)

private theorem result_keeps {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT (Local n) (StateT Platform ProbComp) (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))))
    (law : ∀ value, Keeps localProject (next value)) :
    Keeps localProject (RegistrationNativePlatformServerCompletion.continueResult action next) := by
  cases action with
  | fail error | div => exact pure_keeps localProject _
  | ok answer => cases answer with
    | Err previous => exact pure_keeps localProject _
    | Ok value => exact law value

/-- The actual complete source publication/install suffix preserves cached signing receipts through every writer and insertion outcome. -/
theorem afterRecord (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    Keeps (localProject (n := n)) (RegistrationNativePlatformSourceBuildCut.afterRecord coins sign writer control hashed) := by
  unfold RegistrationNativePlatformSourceBuildCut.afterRecord
  exact bind_keeps localProject _ _
    (fun before previous result valid supported => RegistrationNativePlatformServerPublicationCached.program sign writer hashed before previous result valid supported)
    (fun published => result_keeps _ _ (install control))

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem pin : Keeps (Platform := Platform) (serverProject (n := n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  apply frame_keeps
  intro before previous result supported
  have extension := RegistrationNativePlatformBuildCache.pin coins before previous result supported
  have original := supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, map_apply, support_map] at original
  obtain ⟨inner, _called, same⟩ := original
  exact ⟨(congrArg (fun value => value.1.2.world.world.2) same).symm, extension⟩

private theorem reserve (work : StateT Platform ProbComp Bool) :
    Keeps (serverProject (n := n)) (StateT.lift work) := by
  intro before previous result valid supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  exact valid

private theorem present (keyId : U64) :
    Keeps (Platform := Platform) (serverProject (n := n)) (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId) := by
  apply frame_keeps
  intro before previous result supported
  have extension := RegistrationNativePlatformBuildCache.present coins keyId before previous result supported
  have original := supported
  simp only [RegistrationNativePlatformCompletionSdk.nativePresent, RegistrationNativePlatformServerSdk.world,
    RegistrationNativePlatformServerCompletion.capability, RegistrationNativePlatformServerCompletion.liftNative,
    RegistrationWorldServerCompletion.capability, StateT.run, simulateQ_map, map_apply, Functor.map_map, support_map] at original
  obtain ⟨inner, _called, same⟩ := original
  exact ⟨(congrArg (fun value => value.1.2.world.world.2) same).symm, extension⟩

/-- AD hashing preserves existing signing receipts while executing its actual shared hash query. -/
theorem adHash (pending : registration.ServerAdHash) :
    Keeps (Platform := Platform) (serverProject (n := n)) (RegistrationNativePlatformCompletionSdk.nativeAdHash coins pending) := by
  apply RegistrationNativePlatformSdkCached.world
  unfold RegistrationNativePlatformServerCompletion.adHash RegistrationNativePlatformServerCompletion.adHashWith RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div => exact pure_keeps localProject _
  | ok request =>
      simp only [bind_assoc, pure_bind]
      apply bind_keeps localProject _ _ (capability (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))
      intro _digest
      exact pure_keeps localProject _

variable [primitive : AdapterSealPrimitive.Operations]

/-- Actual first-record execution and its complete response suffix retain all prior and newly attempted cached signing receipts. -/
theorem finish (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps (localProject (n := n)) (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control initial) := by
  intro before previous result valid supported
  obtain ⟨recorded, current, platform, called, continued⟩ := RegistrationNativePlatformSourceBuildCut.cut coins setup codec view failure allocation erased sign helper writer
    control initial before result.1.2 previous result.2 result.1.1 supported
  obtain ⟨extension, receipts⟩ := RegistrationNativePlatformSourceFrames.record_frame coins setup codec view failure allocation erased helper initial
    before previous (recorded, current) platform called
  have recordedValid : RegistrationSigningShared.Cached (localProject current) := by
    change RegistrationSigningShared.Cached (current.world.2, current.world.1.primitive.2)
    rw [receipts]
    exact RegistrationSigningShared.cached_extend _ _ _ extension valid
  cases recorded with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerCompletion.continueResult, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    have stateEq := congrArg (fun value => value.1.2) continued
    exact stateEq ▸ recordedValid
  | ok answer => cases answer with
    | Err prior =>
      simp only [RegistrationNativePlatformServerCompletion.continueResult, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      have stateEq := congrArg (fun value => value.1.2) continued
      exact stateEq ▸ recordedValid
    | Ok hashed => exact afterRecord sign writer control hashed current platform result recordedValid continued

/-- The literal complete stateful source SDK build preserves validity of all same-run ML signing receipts, including moved tokens and every failed prefix. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps (serverProject (n := n))
      (RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer handle application) := by
  unfold RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformSourceBuild.buildSource
  exact RegistrationNativePlatformSdkCached.build _ adHash _ pin _ (reserve reservePeer) _ present _
    (finish setup codec view failure allocation erased sign helper writer) handle application

end BeaconcryptCore.Computational.RegistrationNativePlatformServerCached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.afterRecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.afterRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.adHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCached.adHash
