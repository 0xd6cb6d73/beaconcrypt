-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree
/-! The corrected moved-token Server frontend has one possible material-service request. Its source-derived stateful seal, hash, signing and writer implementations expose no further material demand, while every allocation and failure path remains present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps
open RegistrationNativePlatformServerFrontendProgram (Spec pin reserve present service)
open RegistrationNativePlatformServerMaterialFrontend (Result)
variable {n : Nat}

def IsService : RegistrationNativePlatformServerFrontendProgram.Spec.Domain → Prop
  | .service _ _ _ => True
  | _ => False
instance : DecidablePred IsService := fun query => by
  cases query <;> dsimp [IsService] <;> infer_instance

def IsDemand : (RegistrationNativePlatformServerFrontendCompiler.Spec n).Domain → Prop
  | .inl _ => True
  | _ => False
instance {n : Nat} : DecidablePred (IsDemand (n := n)) := fun query => by
  cases query <;> dsimp [IsDemand] <;> infer_instance

private theorem afterResult (control : pqxdh.ServerState) (reference : RegistrationNativeRelatedFamily.Message)
    (result : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.afterResult reserve service control reference result).run before).IsQueryBoundP IsService 1 := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok selected =>
      simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, StateT.run_bind,
        StateT.run_lift, reserve, bind_pure_comp, bind_map_left]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [IsService], ?_⟩
      intro admitted
      cases admitted with
      | false => trivial
      | true =>
        simp only [ite_true, StateT.run_bind, StateT.run_lift, service, bind_pure_comp, bind_map_left]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨by simp [IsService], fun _ => by trivial⟩

private theorem afterOccupancy (control : pqxdh.ServerState) (lookup : peer.CompletionLookup)
    (reference : RegistrationNativeRelatedFamily.Message) (occupied : Bool)
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.afterOccupancy reserve service control lookup reference occupied).run before).IsQueryBoundP IsService 1 :=
  afterResult control reference _ before

private theorem afterPin (control : pqxdh.ServerState) (ready : RegistrationServerReferenceRoot.Ready)
    (application : Slice U8) (current : RustM (core.option.Option session.ServerAuthenticationPin))
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.afterPin reserve present service control ready application current).run before).IsQueryBoundP IsService 1 := by
  unfold RegistrationNativePlatformServerMaterialFrontend.afterPin StateT.run
  cases current with
  | fail error | div => trivial
  | ok current => cases current with
    | none => trivial
    | some current =>
      dsimp only
      cases peer.begin_completion_lookup control current (RegistrationServerMaterialFrontend.token ready) application with
      | fail error | div => trivial
      | ok answer => cases answer with
        | Err previous => trivial
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error | div => trivial
          | ok keyId =>
            dsimp only
            split
            · unfold present
              rw [isQueryBoundP_query_bind_iff]
              exact ⟨by simp [IsService], fun occupied => afterOccupancy control lookup ready.reference occupied before⟩
            · trivial

private theorem complete (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.complete pin reserve present service ready application).run before).IsQueryBoundP IsService 1 := by
  unfold RegistrationNativePlatformServerMaterialFrontend.complete StateT.run pin
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨by simp [IsService], fun current => afterPin before.control ready application current before⟩

/-- The actual source frontend can reach its material-service leaf at most once. -/
theorem program (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before).IsQueryBoundP IsService 1 := by
  unfold RegistrationNativePlatformServerFrontendProgram.program RegistrationNativePlatformServerMaterialFrontend.build StateT.run
  cases RegistrationServerMaterialFrontend.take handle before with
  | mk selected current => cases selected with
    | none => trivial
    | some ready => cases application with
      | none => trivial
      | some application => exact complete ready application current

private theorem effects_free {A : Type} (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A) :
    (simulateQ RegistrationNativePlatformServerFrontendCompiler.embed work).IsQueryBoundP (IsDemand (n := n)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativePlatformServerFrontendCompiler.embed, IsDemand, isQueryBoundP_query_iff]

variable {E Platform : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : StateT Platform ProbComp Bool)

private theorem target_bound (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain)
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    ((RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reserve query).run before).IsQueryBoundP
      (IsDemand (n := n)) (if IsService query then 1 else 0) := by
  cases query with
  | pin current | reserve | present keyId => exact effects_free _
  | service control initial message =>
    simp only [RegistrationNativePlatformServerFrontendCompiler.target,
      RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind,
      StateT.run_lift, bind_pure_comp, bind_map_left, IsService, ite_true]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [IsDemand], ?_⟩
    intro choice
    cases choice with
    | none => trivial
    | some choice => exact effects_free _

/-- Lowering the literal corrected frontend keeps its single material-demand allowance, for arbitrary persistent allocator and writer computations. -/
theorem build (handle : Nat) (application : Option (Slice U8))
    (front : RegistrationServerMaterialFrontend.State) (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reserve)
      ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before).IsQueryBoundP
      (IsDemand (n := n)) 1 := by
  apply (program handle application front).simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using target_bound source view failure allocation erased helper sign writer reserve query current
  · intro query free current
    simpa only [ite_eq_right free] using target_bound source view failure allocation erased helper sign writer reserve query current
end BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps.build
