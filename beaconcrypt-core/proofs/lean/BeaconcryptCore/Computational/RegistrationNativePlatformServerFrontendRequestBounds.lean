-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram
/-! The literal moved-token Server frontend reaches at most four request leaves, including refused pin, occupancy, reservation and material-service outcomes. This is a source-syntax bound before the individual leaves are lowered to shared hash, native coin and public platform operations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendRequestBounds
open RegistrationNativePlatformServerFrontendProgram (Spec pin reserve present service)
open RegistrationNativePlatformServerMaterialFrontend (Result)

private theorem afterResult (control : pqxdh.ServerState) (reference : RegistrationNativeRelatedFamily.Message)
    (result : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.afterResult reserve service control reference result).run before).IsTotalQueryBound 2 := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok selected =>
      simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, StateT.run_bind,
        StateT.run_lift, reserve, bind_pure_comp, bind_map_left]
      rw [isTotalQueryBound_query_bind_iff]
      refine ⟨by decide, ?_⟩
      intro admitted
      cases admitted with
      | false => trivial
      | true =>
        simp only [ite_true, StateT.run_bind, StateT.run_lift, service, bind_pure_comp, bind_map_left]
        rw [isTotalQueryBound_query_bind_iff]
        exact ⟨by decide, fun _ => by trivial⟩

private theorem afterOccupancy (control : pqxdh.ServerState) (lookup : peer.CompletionLookup)
    (reference : RegistrationNativeRelatedFamily.Message) (occupied : Bool)
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.afterOccupancy reserve service control lookup reference occupied).run before).IsTotalQueryBound 2 :=
  afterResult control reference _ before

private theorem afterPin (control : pqxdh.ServerState) (ready : RegistrationServerReferenceRoot.Ready)
    (application : Slice U8) (current : RustM (core.option.Option session.ServerAuthenticationPin))
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.afterPin reserve present service control ready application current).run before).IsTotalQueryBound 3 := by
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
              rw [isTotalQueryBound_query_bind_iff]
              exact ⟨by decide, fun occupied => afterOccupancy control lookup ready.reference occupied before⟩
            · trivial

private theorem complete (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerMaterialFrontend.complete pin reserve present service ready application).run before).IsTotalQueryBound 4 := by
  unfold RegistrationNativePlatformServerMaterialFrontend.complete StateT.run pin
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun current => afterPin before.control ready application current before⟩

/-- Every actual source frontend path has at most its four literal requests; handle cancellation and all failed-prefix paths use their own smaller prefixes. -/
theorem program (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State) :
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before).IsTotalQueryBound 4 := by
  unfold RegistrationNativePlatformServerFrontendProgram.program RegistrationNativePlatformServerMaterialFrontend.build StateT.run
  cases RegistrationServerMaterialFrontend.take handle before with
  | mk selected current => cases selected with
    | none => trivial
    | some ready => cases application with
      | none => trivial
      | some application => exact complete ready application current
end BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendRequestBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendRequestBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendRequestBounds.program
