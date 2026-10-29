-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence
import BeaconcryptCore.Computational.RegistrationServerMaterialFrontend

/-! Retained native capabilities carry an internal live-root invariant. It is initialized by the empty session list, extended only with actual prepare receipts, preserved by memo extension, and weakened when a one-use handle is taken. No public security event acquires a new root-membership premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialRoots
open RegistrationServerMaterialFrontend (State retain take)
open RegistrationServerReferenceRoot (Ready)
open RegistrationNativeRetainedRoots (Memo)

def Live (state : State) (memo : Memo) : Prop :=
  ∀ ready, some ready ∈ state.sessions → ∃ root, memo ready.reference = some root

/-- Generated empty session state has no unprepared retained capability. -/
theorem initial (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin) (memo : Memo) :
    Live (RegistrationServerMaterialFrontend.initial control pin) memo := by
  intro ready member
  simp [RegistrationServerMaterialFrontend.initial] at member

/-- The actual private memo extension law preserves every still-live native capability. -/
theorem mono (before after : Memo) (state : State)
    (extension : ∀ message root, before message = some root → after message = some root)
    (live : Live state before) : Live state after := by
  intro ready member
  obtain ⟨root, stored⟩ := live ready member
  exact ⟨root, extension ready.reference root stored⟩

private theorem mem_set_none (sessions : List (Option Ready)) (handle : Nat) (ready : Ready)
    (member : some ready ∈ sessions.set handle none) : some ready ∈ sessions := by
  induction sessions generalizing handle with
  | nil => simp at member
  | cons head rest ih =>
      cases handle with
      | zero =>
          simp only [List.set_cons_zero, List.mem_cons] at member
          rcases member with impossible | earlier
          · cases impossible
          · exact List.mem_cons_of_mem _ earlier
      | succ handle =>
          simp only [List.set_cons_succ, List.mem_cons] at member
          rcases member with same | earlier
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons_of_mem _ (ih handle earlier)

/-- Taking or cancelling any handle preserves every other live capability and yields an already prepared root when it succeeds. -/
theorem take_live (handle : Nat) (before : State) (memo : Memo) (live : Live before memo) :
    Live (take handle before).2 memo ∧
      ∀ ready, (take handle before).1 = some ready → ∃ root, memo ready.reference = some root := by
  unfold take
  cases lookup : before.sessions[handle]? with
  | none => exact ⟨live, fun _ impossible => by cases impossible⟩
  | some entry => cases entry with
    | none => exact ⟨live, fun _ impossible => by cases impossible⟩
    | some ready =>
        refine ⟨?_, ?_⟩
        · intro other member
          exact live other (mem_set_none before.sessions handle other member)
        · intro other same
          cases same
          exact live ready (List.mem_of_getElem? lookup)

/-- Actual native replay/retention extends the invariant only with the root receipt supplied by its successful preparation. -/
theorem retain_live (ready : Ready) (before after : State) (memo : Memo)
    (live : Live before memo) (prepared : ∃ root, memo ready.reference = some root)
    (reply : Option Nat) (actual : retain ready before = .ok (reply, after)) : Live after memo := by
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.consumed with
  | fail error => simp only [retain, consumed] at actual; cases actual
  | div => simp only [retain, consumed] at actual; cases actual
  | ok pair =>
      rcases pair with ⟨entry, history⟩
      cases entry with
      | none =>
          simp only [retain, consumed, RustM.ok.injEq, Prod.mk.injEq] at actual
          rcases actual with ⟨rfl, rfl⟩
          exact live
      | some token =>
          simp only [retain, consumed, RustM.ok.injEq, Prod.mk.injEq] at actual
          rcases actual with ⟨rfl, rfl⟩
          intro other member
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
          rcases member with earlier | same
          · exact live other earlier
          · cases same
            exact prepared

end BeaconcryptCore.Computational.RegistrationServerMaterialRoots
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialRoots.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialRoots.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialRoots.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialRoots.mono
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialRoots.take_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialRoots.take_live
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialRoots.retain_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialRoots.retain_live
