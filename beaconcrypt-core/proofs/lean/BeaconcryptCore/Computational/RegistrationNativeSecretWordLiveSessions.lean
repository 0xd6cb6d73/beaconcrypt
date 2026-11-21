-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial

/-! Actual retained symbolic capabilities carry their preparation flag. Empty sessions establish the invariant, checked flag extension preserves it, native retention adds only its actual prepared reference, and taking a one-use handle removes entries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions
open RegistrationNativeSecretWordServerMaterial (State retain take)
open RegistrationNativeSecretWordService (Flags)
open RegistrationNativeSecretWordMessage (ServerReady)
abbrev Ready := ServerReady

def Live (state : State) (flags : Flags) : Prop :=
  ∀ ready, some ready ∈ state.sessions → flags ready.reference = true

/-- Empty sessions contain no unprepared reference. -/
theorem initial (state : State) (flags : Flags) (empty : state.sessions = []) : Live state flags := by
  intro ready member
  simp only [empty, List.not_mem_nil] at member

/-- The actual private memo extension law preserves every still-live native capability. -/
theorem mono (before after : Flags) (state : State)
    (extension : ∀ message, before message = true → after message = true)
    (live : Live state before) : Live state after := by
  intro ready member
  exact extension ready.reference (live ready member)

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
theorem take_live (handle : Nat) (before : State) (flags : Flags) (live : Live before flags) :
    Live (take handle before).2 flags ∧
      ∀ ready, (take handle before).1 = some ready → flags ready.reference = true := by
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
theorem retain_live (ready : Ready) (before after : State) (flags : Flags)
    (live : Live before flags) (prepared : flags ready.reference = true)
    (reply : Option Nat) (actual : retain ready before = .ok (reply, after)) : Live after flags := by
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.consumed with
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

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.mono
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.take_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.take_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.retain_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions.retain_live
