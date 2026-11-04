-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut

/-! The corrected source Server completion reifies only its actual response ML leaf. Its source first-record allocator, trusted AEAD, mutable hash, raw writer, response serializer, moved handles and installation retain one shared external platform state. Evaluating the named ML capability restores literal source completion, including every failed prefix. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformMldsaProgram (M evaluate lift inject coins)
variable {n : Nat} {E Auxiliary Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := bind_pure_comp _ _

noncomputable def outgoing (query : RegistrationSigningShared.Spec.Domain) :
    StateT (State n Auxiliary) (M source Platform) (RegistrationSigningShared.Spec.Range query) :=
  inject (fun before => (fun result => (result.1, { before with world := result.2 })) <$>
    (RegistrationNativeMldsaServer.outgoing source credential query).run before.world)

private theorem local_outgoing (query : RegistrationSigningShared.Spec.Domain) :
    RegistrationNativeMldsaProgram.evalState (fun before : State n Auxiliary =>
      (fun result => (result.1, { before with world := result.2 })) <$>
        (RegistrationNativeMldsaServer.outgoing source credential query).run before.world) =
      RegistrationNativePlatformServerCompletion.nativeOutgoing (RegistrationNativeMldsa.owned source credential) query := by
  funext before
  have same := congrFun (RegistrationNativeMldsaServer.eval_outgoing (n := n) source credential query) before.world
  simp only [RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate,
    StateT.run, simulateQ_map, RegistrationNativePlatformServerCompletion.nativeOutgoing]
  simp only [RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate, StateT.run] at same
  rw [same]

/-- The named Server ML leaf evaluates to its exact source request, true draws and chronological receipt, retaining external state. -/
theorem evaluate_outgoing (query : RegistrationSigningShared.Spec.Domain) :
    evaluate (outgoing (n := n) (Auxiliary := Auxiliary) (Platform := Platform) source credential query) =
      RegistrationNativePlatformServerCompletion.outgoing coins (RegistrationNativeMldsa.owned source credential) query := by
  rw [outgoing, RegistrationNativePlatformMldsaProgram.evaluate_inject, local_outgoing]
  funext before
  exact (RegistrationNativePlatformMldsaProgram.lift_coins
    ((RegistrationNativePlatformServerCompletion.nativeOutgoing (RegistrationNativeMldsa.owned source credential) query).run before)).symm

variable [primitive : AdapterSealPrimitive.Operations]

noncomputable def afterRecord
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    StateT (RegistrationServerRootCompiler.Local n) (M source Platform)
      (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) := do
  let published ← RegistrationNativePlatformServerPublication.program
    (outgoing source credential) (fun view => lift (RegistrationNativePlatformSourceBuild.encode writer view)) hashed
  RegistrationNativePlatformServerCompletion.continueResult published fun ready =>
    lift (RegistrationNativePlatformServerCompletion.installWith
      (RegistrationNativePlatformServerCompletion.capability coins) control ready)

omit primitive in
/-- The full response hash/sign/source-writer/install continuation evaluates to the corrected source continuation. -/
theorem evaluate_afterRecord
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    evaluate (afterRecord (n := n) source credential writer control hashed) =
      RegistrationNativePlatformSourceBuildCut.afterRecord coins (RegistrationNativeMldsa.owned source credential)
        writer control hashed := by
  unfold afterRecord RegistrationNativePlatformSourceBuildCut.afterRecord
  rw [RegistrationNativePlatformMldsaProgram.evaluate_bind]
  have publication := RegistrationNativePlatformBuildInterpret.Publication.program
    (RegistrationNativePlatformMldsaProgram.evaluate_hom (Native := RegistrationServerRootCompiler.Local n) (source := source) (Platform := Platform))
    (outgoing source credential) (fun view => lift (RegistrationNativePlatformSourceBuild.encode writer view)) hashed
  simp only [evaluate_outgoing, RegistrationNativePlatformMldsaProgram.evaluate_lift] at publication
  rw [publication]
  apply bind_congr
  intro published
  cases published with
  | fail error | div => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
    | Ok ready => exact RegistrationNativePlatformMldsaProgram.evaluate_lift _

noncomputable def finish (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    StateT (RegistrationServerRootCompiler.Local n) (M source Platform)
      (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) := do
  let recorded ← lift (RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial)
  RegistrationNativePlatformServerCompletion.continueResult recorded (afterRecord source credential writer control)

/-- Literal source first-record allocation and all later publication failures survive actual ML capability evaluation. -/
theorem evaluate_finish (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    evaluate (finish (n := n) source credential setup codec view failure allocation erased helper writer control initial) =
      RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
        (RegistrationNativeMldsa.owned source credential) helper writer control initial := by
  unfold finish
  rw [RegistrationNativePlatformMldsaProgram.evaluate_bind, RegistrationNativePlatformMldsaProgram.evaluate_lift]
  change _ = (do
    let recorded ← RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial
    RegistrationNativePlatformServerCompletion.continueResult recorded
      (RegistrationNativePlatformSourceBuildCut.afterRecord coins (RegistrationNativeMldsa.owned source credential) writer control))
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
    | Ok hashed => exact evaluate_afterRecord source credential writer control hashed

omit primitive in
private theorem evaluate_world {Value : Type}
    (work : StateT (RegistrationServerRootCompiler.Local n) (M source Platform) Value) :
    evaluate (RegistrationNativePlatformServerSdk.world work) =
      RegistrationNativePlatformServerSdk.world (evaluate work) := by
  funext before previous
  simp only [evaluate, RegistrationNativePlatformServerSdk.world,
    RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate,
    StateT.run, state_map_apply, simulateQ_map]

omit primitive in
private theorem evaluate_commit
    (published : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) :
    evaluate (RegistrationNativePlatformServerSdk.commit (n := n) (m := M source Platform) published) =
      RegistrationNativePlatformServerSdk.commit published := by
  cases published with
  | fail error | div => funext before previous; rfl
  | ok answer => cases answer <;> funext before previous <;> rfl

omit primitive in
private theorem evaluate_fromInitial
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M source Platform) (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    evaluate (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) =
      RegistrationNativePlatformCompletionSdk.fromInitial (fun control initial => evaluate (finish control initial)) control initial := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  rw [RegistrationNativePlatformMldsaProgram.evaluate_bind, evaluate_world]
  apply bind_congr
  intro published
  exact evaluate_commit source published

omit primitive in
private theorem evaluate_afterOccupancy
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M source Platform) (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    evaluate (RegistrationNativePlatformCompletionSdk.afterOccupancy reserve finish control lookup occupied) =
      RegistrationNativePlatformCompletionSdk.afterOccupancy (evaluate reserve)
        (fun control initial => evaluate (finish control initial)) control lookup occupied := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
    | Ok initial =>
        rw [RegistrationNativePlatformMldsaProgram.evaluate_bind]
        apply bind_congr
        intro admitted
        cases admitted with
        | false => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
        | true => exact evaluate_fromInitial source finish control initial

omit primitive in
private theorem evaluate_afterPin
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M source Platform) (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (Option session.ServerAuthenticationPin)) :
    evaluate (RegistrationNativePlatformCompletionSdk.afterPin reserve present finish control token application pin) =
      RegistrationNativePlatformCompletionSdk.afterPin (evaluate reserve) (fun keyId => evaluate (present keyId))
        (fun control initial => evaluate (finish control initial)) control token application pin := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
  | ok optional => cases optional with
    | none => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
    | some pin =>
        dsimp only
        cases peer.begin_completion_lookup control pin token application with
        | fail error | div => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
        | ok answer => cases answer with
          | Err prior => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
          | Ok lookup =>
              dsimp only
              cases lookup.request with
              | fail error | div => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
              | ok keyId =>
                  dsimp only
                  split
                  · rw [RegistrationNativePlatformMldsaProgram.evaluate_bind]
                    apply bind_congr
                    intro occupied
                    exact evaluate_afterOccupancy source reserve finish control lookup occupied
                  · exact RegistrationNativePlatformMldsaProgram.evaluate_pure _

omit primitive in
private theorem evaluate_complete
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M source Platform) (alloc.vec.Vec U8))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    evaluate (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application) =
      RegistrationNativePlatformCompletionSdk.complete (evaluate pin) (evaluate reserve) (fun keyId => evaluate (present keyId))
        (fun control initial => evaluate (finish control initial)) token application := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  rw [RegistrationNativePlatformMldsaProgram.evaluate_bind]
  have sameGet : evaluate (get : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) _) = get := by
    funext before previous
    rfl
  rw [sameGet]
  apply bind_congr
  intro before
  rw [RegistrationNativePlatformMldsaProgram.evaluate_bind]
  apply bind_congr
  intro selected
  exact evaluate_afterPin source reserve present finish before.control token application selected

omit primitive in
private theorem evaluate_sdk
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M source Platform) (alloc.vec.Vec U8))
    (handle : Nat) (application : Option (Slice U8)) :
    evaluate (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application) =
      RegistrationNativePlatformCompletionSdk.build (evaluate pin) (evaluate reserve) (fun keyId => evaluate (present keyId))
        (fun control initial => evaluate (finish control initial)) handle application := by
  funext before
  simp only [evaluate, RegistrationNativePlatformCompletionSdk.build, StateT.run]
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk selected current =>
      cases selected with
      | none => funext previous; rfl
      | some token => cases application with
        | none => funext previous; rfl
        | some application => exact congrFun (evaluate_complete source pin reserve present finish token application) current

noncomputable def build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (Option (U64 × alloc.vec.Vec U8))) :=
  RegistrationNativePlatformCompletionSdk.build
    (lift (RegistrationNativePlatformSourceBuild.pin coins))
    (lift (StateT.lift reservePeer))
    (fun keyId => lift (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId))
    (finish source credential setup codec view failure allocation erased helper writer) handle application

/-- The entire stateful source SDK build, including repeated pin hashing and failed publication, is an exact ML capability program. -/
theorem evaluate_build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    evaluate (build (n := n) source credential setup codec view failure allocation erased reservePeer helper writer handle application) =
      RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer
        (RegistrationNativeMldsa.owned source credential) helper writer handle application := by
  rw [build, evaluate_sdk]
  simp only [RegistrationNativePlatformMldsaProgram.evaluate_lift, evaluate_finish]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_afterRecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_afterRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer.evaluate_build
