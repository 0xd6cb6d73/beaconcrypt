-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
/-! Event transport changes only analysis snapshots, preserving the original packet and exact public cut. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeObservedStageTrace (mapCall)
open RegistrationNativeIdentityUnissuedCutTrace (accepted)
open RegistrationNativeIdentityUnissuedCutEvent (At AtCut)
variable {S T A : Type}

/-- Observed accepted attempts retain their same order and literal packets. -/
theorem accepted_map (observe : S → T) (calls : List (Call TypedSpec S)) :
    accepted (calls.map (mapCall observe)) = (accepted calls).map (fun entry => (entry.1,observe entry.2)) := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
      cases query : call.query with
      | inl coin => simpa only [List.map_cons,accepted,mapCall,query,List.filterMap_cons,List.map_cons] using ih
      | inr command => cases command <;> simp_all [accepted,mapCall]

/-- The same fixed ordinal event is preserved when only its before-state observation is projected. -/
theorem at_map (observe : S → T) (bad : beaconcrypt_core.registration.InitPacket → T → Prop)
    (accept : Nat) (value : A) (before : S) (calls : List (Call TypedSpec S)) :
    At bad accept (value,(observe before,calls.map (mapCall observe))) ↔
      At (fun packet state => bad packet (observe state)) accept (value,(before,calls)) := by
  simp only [At,accepted_map,List.getElem?_map]
  constructor
  · rintro ⟨packet,previous,found,failed⟩
    obtain ⟨entry,selected,equal⟩ := Option.map_eq_some_iff.mp found
    cases equal
    exact ⟨entry.1,entry.2,selected,failed⟩
  · rintro ⟨packet,previous,found,failed⟩
    refine ⟨packet,observe previous,?_,failed⟩
    rw [found]
    rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection.accepted_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection.accepted_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection.at_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection.at_map
