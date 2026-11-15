-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle

/-! The private client analysis projection omits only the indexed KEM pool. Actual protected unsigned-origin cuts and the final shared-cache collision factor through it; all owner credentials, source cache and signing histories remain retained. This is private proof metadata and is not an adversary-visible view. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemClientObservation
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeKemServerState (State ofNative toNative)
open RegistrationNativeStageTrace (Call)
variable {n : Nat} {KemSK Platform : Type} {source : Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Client" => State n source

def bad (server : Credential source) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : Client) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) : Prop :=
  RegistrationNativeMldsaOriginEvent.Bad source server query (toNative before (PqxdhLiveKemBirth.empty : PqxdhLiveKemBirth.Pool KemSK)) reply

/-- Actual protected origin failure depends on the retained source metadata and signing prefix, independently of the private KEM pool. -/
theorem bad_native (server : Credential source) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : Native) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    bad (KemSK := KemSK) server query (ofNative before) reply ↔ RegistrationNativeMldsaOriginEvent.Bad source server query before reply := by
  unfold bad
  constructor
  · intro failure
    cases failure with
    | finish index packet application _ current pending oneTime found phase protectedKey absent =>
        exact .finish index packet application before current pending oneTime found phase protectedKey absent
  · intro failure
    cases failure with
    | finish index packet application _ current pending oneTime found phase protectedKey absent =>
        exact .finish index packet application _ current pending oneTime found phase protectedKey absent

/-- The shared source cache is retained literally when the private KEM pool is separated. -/
theorem cache_native (before : Native) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    RegistrationNativeWorldCache.cache (toNative (ofNative before) pool) = RegistrationNativeWorldCache.cache before := rfl

def call (original : Call RegistrationNativeRawAdapter.TypedSpec (Native × Platform)) :
    Call RegistrationNativeRawAdapter.TypedSpec (Client × Platform) :=
  ⟨original.query, (ofNative original.before.1, original.before.2), original.reply,
    (ofNative original.after.1, original.after.2)⟩

def BadCalls (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec (Client × Platform))) : Prop :=
  ∃ current ∈ calls, bad (KemSK := KemSK) server current.query current.before.1 current.reply

noncomputable def flagged (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec (Client × Platform))) : Bool := by
  classical
  exact calls.any fun current => decide (bad (KemSK := KemSK) server current.query current.before.1 current.reply)

/-- The same-run chronological bad-cut event is preserved by projecting each actual pre/post state to its client representation. -/
theorem bad_calls (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec (Native × Platform))) :
    BadCalls (KemSK := KemSK) server (calls.map call) ↔ RegistrationNativePlatformMldsaOriginJournal.BadCalls server calls := by
  constructor
  · rintro ⟨current, member, failure⟩
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    subst current
    exact ⟨original, originalMember, (bad_native server original.query original.before.1 original.reply).mp failure⟩
  · rintro ⟨original, member, failure⟩
    exact ⟨call original, List.mem_map.mpr ⟨original, member, rfl⟩,
      (bad_native server original.query original.before.1 original.reply).mpr failure⟩

/-- The actual source journal's origin marker is exactly the client-projected private marker, with unchanged chronology. -/
theorem flagged_native (server : Credential source) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec (Native × Platform))) :
    flagged (KemSK := KemSK) server (calls.map call) = RegistrationNativePlatformMldsaOriginJournal.flagged server calls := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [RegistrationNativePlatformMldsaOriginJournal.flagged_iff]
  rw [← bad_calls server calls]
  simp only [flagged, BadCalls, List.any_eq_true, decide_eq_true_eq]
end BeaconcryptCore.Computational.RegistrationNativeKemClientObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.bad_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.bad_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.cache_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.cache_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.bad_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.bad_calls

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.flagged_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemClientObservation.flagged_native
