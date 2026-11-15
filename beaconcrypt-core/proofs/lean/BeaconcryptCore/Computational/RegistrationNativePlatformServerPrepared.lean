-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries
/-! The actual corrected one-use Server build can demand only the root of the Ready token that it took. The property is derived for every pin, occupancy, stateful reservation and publication reply; live-root data is an internal source invariant, not a restriction on the final public event. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerPrepared
open RegistrationNativeRetainedRoots (Memo)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativePlatformServerFrontendProgram (Spec adHash pin reserve present service program)
open RegistrationNativePlatformServerMaterialFrontend (afterResult afterOccupancy afterPin complete build)
open RegistrationServerMaterialFrontend (State)
open RegistrationServerReferenceRoot (Ready)

def Backed (memo : Memo) (roots : Roots) : Spec.Domain → Prop
  | .service _ _ message => memo message = some (roots message)
  | _ => True

private theorem result_backed (memo : Memo) (roots : Roots)
    (control : pqxdh.ServerState) (message : RegistrationNativeRelatedFamily.Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : State) (stored : memo message = some (roots message)) :
    ((afterResult reserve service control message action).run before).AllQueriesSatisfy (Backed memo roots) := by
  cases action with
  | fail error => trivial
  | div => trivial
  | ok answer => cases answer with
    | Err previous => trivial
    | Ok selected =>
      simp only [afterResult, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left,
        reserve, allQueriesSatisfy_query_bind_iff]
      refine ⟨trivial, ?_⟩
      intro allocated
      cases allocated with
      | false => trivial
      | true =>
          simp only [ite_true, StateT.run_bind, StateT.run_lift, bind_pure_comp,
            bind_map_left, service, allQueriesSatisfy_query_bind_iff]
          exact ⟨stored, fun _ => trivial⟩

private theorem occupancy_backed (memo : Memo) (roots : Roots) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (message : RegistrationNativeRelatedFamily.Message) (occupied : Bool)
    (before : State) (stored : memo message = some (roots message)) :
    ((afterOccupancy adHash reserve service control lookup message occupied).run before).AllQueriesSatisfy
      (Backed memo roots) := by
  unfold afterOccupancy
  cases resumed : lookup.resume occupied with
  | fail error | div => trivial
  | ok answer => cases answer with
    | Err previous => trivial
    | Ok pending =>
        simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left,
          adHash, allQueriesSatisfy_query_bind_iff]
        exact ⟨trivial, fun hashed => result_backed memo roots control message _ before stored⟩

private theorem pin_backed (memo : Memo) (roots : Roots) (control : pqxdh.ServerState)
    (ready : Ready) (application : Slice U8) (current : RustM (core.option.Option session.ServerAuthenticationPin))
    (before : State) (stored : memo ready.reference = some (roots ready.reference)) :
    ((afterPin adHash reserve present service control ready application current).run before).AllQueriesSatisfy (Backed memo roots) := by
  cases current with
  | fail error => trivial
  | div => trivial
  | ok optional => cases optional with
    | none => trivial
    | some current =>
      unfold afterPin
      dsimp! only
      cases peer.begin_completion_lookup control current (RegistrationServerMaterialFrontend.token ready) application with
      | fail error => trivial
      | div => trivial
      | ok answer => cases answer with
        | Err previous => trivial
        | Ok selected =>
          cases requested : selected.request with
          | fail error => trivial
          | div => trivial
          | ok keyId =>
            simp only [requested]
            split
            · simp only [present]
              exact ⟨trivial, fun occupied => occupancy_backed memo roots control selected ready.reference occupied before stored⟩
            · trivial

/-- Completion never changes the demanded descriptor, even after stateful pin/reservation failures. -/
theorem complete_backed (memo : Memo) (roots : Roots) (ready : Ready) (application : Slice U8)
    (before : State) (stored : memo ready.reference = some (roots ready.reference)) :
    ((complete adHash pin reserve present service ready application).run before).AllQueriesSatisfy (Backed memo roots) := by
  simp only [complete, StateT.run, pin, allQueriesSatisfy_query_bind_iff]
  exact ⟨trivial, fun current => pin_backed memo roots before.control ready application current before stored⟩

/-- Every material demand of the literal corrected build is backed by the earlier private preparation of its moved handle. -/
theorem build_backed (memo : Memo) (roots : Roots) (handle : Nat) (application : Option (Slice U8))
    (before : State) (live : RegistrationServerMaterialRoots.Live before memo)
    (consistent : ∀ message root, memo message = some root → roots message = root) :
    ((program handle application).run before).AllQueriesSatisfy (Backed memo roots) := by
  have taken := RegistrationServerMaterialRoots.take_live handle before memo live
  unfold program build
  simp only [StateT.run]
  cases chosen : RegistrationServerMaterialFrontend.take handle before with
  | mk optional current => cases optional with
    | none => trivial
    | some ready =>
      obtain ⟨root, stored⟩ := taken.2 ready (by rw [chosen])
      have literal := consistent ready.reference root stored
      cases application with
      | none => trivial
      | some application => exact complete_backed memo roots ready application current (by simpa only [literal] using stored)

end BeaconcryptCore.Computational.RegistrationNativePlatformServerPrepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPrepared.complete_backed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPrepared.complete_backed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPrepared.build_backed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPrepared.build_backed
