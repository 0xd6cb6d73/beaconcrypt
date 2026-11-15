-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServer
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap

/-! The complete actual stateful Server build translates only its owned ML credential at the named signing leaf. Its native record state, public allocator state, source writers and all failure prefixes stay literal. No equality of closed signers or generation behavior is required. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeMldsaMap (Map credential)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformMldsaSignMap (transform)
variable {left right : RegistrationNativeMldsa.Source} {n : Nat} {E Auxiliary Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := bind_pure_comp _ _

theorem outgoing (mapping : Map left right) (current : RegistrationNativeMldsa.Credential left)
    (query : RegistrationSigningShared.Spec.Domain) :
    transform mapping (RegistrationNativePlatformMldsaServer.outgoing (n := n) (Auxiliary := Auxiliary) (Platform := Platform) left current query) =
      RegistrationNativePlatformMldsaServer.outgoing right (credential mapping current) query := by
  unfold RegistrationNativePlatformMldsaServer.outgoing
  rw [RegistrationNativePlatformMldsaSignMap.inject]
  apply congrArg RegistrationNativePlatformMldsaProgram.inject
  funext before
  have same := congrFun (RegistrationNativeMldsaServerMap.outgoing (n := n) mapping current query) before.world
  simp only [RegistrationNativeMldsaSignMap.transformState, RegistrationNativeMldsaSignMap.transform, StateT.run] at same ⊢
  simp only [simulateQ_map]
  rw [same]

theorem afterRecord (mapping : Map left right) (current : RegistrationNativeMldsa.Credential left)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    transform mapping (RegistrationNativePlatformMldsaServer.afterRecord (n := n) left current writer control hashed) =
      RegistrationNativePlatformMldsaServer.afterRecord right (credential mapping current) writer control hashed := by
  unfold RegistrationNativePlatformMldsaServer.afterRecord
  rw [RegistrationNativePlatformMldsaSignMap.bind]
  have publication := RegistrationNativePlatformBuildInterpret.Publication.program
    (RegistrationNativePlatformMldsaSignMap.hom (Native := RegistrationServerRootCompiler.Local n) (Platform := Platform) mapping)
    (RegistrationNativePlatformMldsaServer.outgoing left current)
    (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformSourceBuild.encode writer view)) hashed
  simp only [outgoing, RegistrationNativePlatformMldsaSignMap.lift] at publication
  rw [publication]
  apply bind_congr
  intro published
  cases published with
  | fail error | div => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
    | Ok ready => exact RegistrationNativePlatformMldsaSignMap.lift mapping _

variable [primitive : AdapterSealPrimitive.Operations]

theorem finish (mapping : Map left right) (current : RegistrationNativeMldsa.Credential left)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    transform mapping (RegistrationNativePlatformMldsaServer.finish (n := n) left current setup codec view failure allocation erased helper writer control initial) =
      RegistrationNativePlatformMldsaServer.finish right (credential mapping current) setup codec view failure allocation erased helper writer control initial := by
  unfold RegistrationNativePlatformMldsaServer.finish
  rw [RegistrationNativePlatformMldsaSignMap.bind, RegistrationNativePlatformMldsaSignMap.lift]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
    | Ok hashed => exact afterRecord mapping current writer control hashed

omit primitive in
private theorem transform_world (mapping : Map left right) {Value : Type}
    (work : StateT (RegistrationServerRootCompiler.Local n) (M left Platform) Value) :
    transform mapping (RegistrationNativePlatformServerSdk.world work) =
      RegistrationNativePlatformServerSdk.world (transform mapping work) := by
  funext before previous
  simp only [transform, RegistrationNativePlatformServerSdk.world,
    RegistrationNativeMldsaSignMap.transform, StateT.run, state_map_apply, simulateQ_map]

omit primitive in
private theorem transform_commit (mapping : Map left right)
    (published : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) :
    transform mapping (RegistrationNativePlatformServerSdk.commit (n := n) (m := M left Platform) published) =
      RegistrationNativePlatformServerSdk.commit published := by
  cases published with
  | fail error | div => funext before previous; rfl
  | ok answer => cases answer <;> funext before previous <;> rfl

omit primitive in
private theorem transform_fromInitial (mapping : Map left right)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M left Platform) (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    transform mapping (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) =
      RegistrationNativePlatformCompletionSdk.fromInitial (fun control initial => transform mapping (finish control initial)) control initial := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  rw [RegistrationNativePlatformMldsaSignMap.bind mapping, transform_world mapping]
  apply bind_congr
  intro published
  exact transform_commit mapping published

omit primitive in
private theorem transform_afterOccupancy (mapping : Map left right)
    (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n (M left Platform))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M left Platform) (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    transform mapping (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) =
      RegistrationNativePlatformCompletionSdk.afterOccupancy (fun pending => transform mapping (deriveAd pending)) (transform mapping reserve)
        (fun control initial => transform mapping (finish control initial)) control lookup occupied := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
    | Ok pending =>
        rw [RegistrationNativePlatformMldsaSignMap.bind mapping]
        apply bind_congr
        intro hashed
        cases hashed with
        | fail error | div => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
        | ok answer => cases answer with
          | Err previous => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
          | Ok initial =>
            rw [RegistrationNativePlatformMldsaSignMap.bind mapping]
            apply bind_congr
            intro admitted
            cases admitted with
            | false => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
            | true => exact transform_fromInitial mapping finish control initial

omit primitive in
private theorem transform_afterPin (mapping : Map left right)
    (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n (M left Platform))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M left Platform) (alloc.vec.Vec U8))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (Option session.ServerAuthenticationPin)) :
    transform mapping (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application pin) =
      RegistrationNativePlatformCompletionSdk.afterPin (fun pending => transform mapping (deriveAd pending)) (transform mapping reserve) (fun keyId => transform mapping (present keyId))
        (fun control initial => transform mapping (finish control initial)) control token application pin := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
  | ok optional => cases optional with
    | none => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
    | some pin =>
        dsimp only
        cases peer.begin_completion_lookup control pin token application with
        | fail error | div => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
        | ok answer => cases answer with
          | Err prior => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
          | Ok lookup =>
              dsimp only
              cases lookup.request with
              | fail error | div => exact RegistrationNativePlatformMldsaSignMap.pure mapping _
              | ok keyId =>
                  dsimp only
                  split
                  · rw [RegistrationNativePlatformMldsaSignMap.bind mapping]
                    apply bind_congr
                    intro occupied
                    exact transform_afterOccupancy mapping deriveAd reserve finish control lookup occupied
                  · exact RegistrationNativePlatformMldsaSignMap.pure mapping _

omit primitive in
private theorem transform_complete (mapping : Map left right)
    (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n (M left Platform))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M left Platform) (alloc.vec.Vec U8))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    transform mapping (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) =
      RegistrationNativePlatformCompletionSdk.complete (fun pending => transform mapping (deriveAd pending)) (transform mapping pin) (transform mapping reserve) (fun keyId => transform mapping (present keyId))
        (fun control initial => transform mapping (finish control initial)) token application := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  rw [RegistrationNativePlatformMldsaSignMap.bind mapping]
  have sameGet : transform mapping (get : StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) _) = get := by
    funext before previous
    rfl
  rw [sameGet]
  apply bind_congr
  intro before
  rw [RegistrationNativePlatformMldsaSignMap.bind mapping]
  apply bind_congr
  intro selected
  exact transform_afterPin mapping deriveAd reserve present finish before.control token application selected

omit primitive in
private theorem transform_sdk (mapping : Map left right)
    (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n (M left Platform))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M left Platform) Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (M left Platform) (alloc.vec.Vec U8))
    (handle : Nat) (application : Option (Slice U8)) :
    transform mapping (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) =
      RegistrationNativePlatformCompletionSdk.build (fun pending => transform mapping (deriveAd pending)) (transform mapping pin) (transform mapping reserve) (fun keyId => transform mapping (present keyId))
        (fun control initial => transform mapping (finish control initial)) handle application := by
  funext before previous
  simp only [transform, RegistrationNativePlatformCompletionSdk.build, StateT.run]
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk selected current =>
      cases selected with
      | none => rfl
      | some token => cases application with
        | none => rfl
        | some application => exact congrFun (congrFun (transform_complete mapping deriveAd pin reserve present finish token application) current) previous

/-- Complete source build key translation preserves its actual shared platform behavior and all source outcomes. -/
theorem build (mapping : Map left right) (current : RegistrationNativeMldsa.Credential left)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    transform mapping (RegistrationNativePlatformMldsaServer.build (n := n) left current setup codec view failure allocation erased reservePeer helper writer handle application) =
      RegistrationNativePlatformMldsaServer.build right (credential mapping current) setup codec view failure allocation erased reservePeer helper writer handle application := by
  rw [RegistrationNativePlatformMldsaServer.build, transform_sdk]
  simp only [RegistrationNativePlatformMldsaSignMap.lift, finish]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.afterRecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.afterRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap.build
