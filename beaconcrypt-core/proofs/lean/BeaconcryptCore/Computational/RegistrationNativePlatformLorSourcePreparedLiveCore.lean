-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape
/-! Retained capabilities refer only to their own earlier actual preparations; consumption removes capabilities and chronological extension preserves their witnesses. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared)
abbrev Trace := RegistrationNativeSecretWordFrontendTrace.State

def Live (server : ServerState) (trace : Trace) : Prop :=
  ∀ready,some ready∈server.sessions→Prepared ready.reference trace
noncomputable def flags (trace : Trace) (message : Message) : Bool := by
  classical
  exact decide (Prepared message trace)

/-- The actual preparation chronology supplies the existing literal build flag interface. -/
theorem flags_live (server : ServerState) (trace : Trace) (live : Live server trace) :
    RegistrationNativeSecretWordLiveSessions.Live server (flags trace) := by
  classical
  intro ready member
  exact decide_eq_true (live ready member)

/-- Appended trace events retain the preparation of every current capability. -/
theorem mono (server : ServerState) (before after : Trace) (added : List RegistrationNativeSecretWordFrontendTrace.Event)
    (appended : after.events=before.events++added) (live : Live server before) : Live server after := by
  intro ready member
  have prepared := live ready member
  dsimp only [Prepared] at prepared ⊢
  rw [appended]
  exact List.mem_append_left _ prepared

/-- The exact actual accept shape introduces only the Ready whose successful returned handle carries its preparation. -/
theorem shape (before after : ServerState) (trace : Trace) (reply : RustM (Option Nat))
    (actual : RegistrationNativeSecretWordAtomSessionShape.Shape before.sessions reply after.sessions)
    (live : Live before trace)
    (newReady : ∀handle,reply=.ok (some handle)→∃ready,after.sessions[handle]?=some (some ready)∧Prepared ready.reference trace) :
    Live after trace := by
  intro ready member
  rcases actual with same|⟨added,same,returned⟩
  · rw [same] at member
    exact live ready member
  · rw [same,List.mem_append,List.mem_singleton] at member
    rcases member with old|newEntry
    · exact live ready old
    · have sameReady : ready=added := Option.some.inj newEntry
      obtain ⟨stored,found,prepared⟩ := newReady before.sessions.length returned
      rw [same,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero] at found
      have storedEq : added=stored := Option.some.inj (Option.some.inj found)
      rw [sameReady,storedEq]
      exact prepared

/-- Taking a one-use session retains every surviving capability's preparation and identifies the moved Ready. -/
theorem take (handle : Nat) (before : ServerState) (trace : Trace) (live : Live before trace) :
    Live (RegistrationNativeSecretWordServerMaterial.take handle before).2 trace ∧
      ∀ready,(RegistrationNativeSecretWordServerMaterial.take handle before).1=some ready→Prepared ready.reference trace := by
  classical
  obtain ⟨surviving,moved⟩ := RegistrationNativeSecretWordLiveSessions.take_live handle before (flags trace) (flags_live before trace live)
  constructor
  · intro ready member
    exact of_decide_eq_true (surviving ready member)
  · intro ready found
    exact of_decide_eq_true (moved ready found)
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.flags_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.flags_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.mono
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore.take
