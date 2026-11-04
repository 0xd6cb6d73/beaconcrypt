-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts

/-! Source weighted bills transport through the literal local/public reference inclusions and selected KEM routing. Every route retains its actual request; no callback frame is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeReferenceCosts
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_simulate)
open RegistrationNativePrimitiveCosts (coinCost)
variable {n : Nat} {KemSK Value : Type}

def bill (qSign qKem : Nat) : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain → EffectKind → Nat
  | .inl _, _ => 0
  | .inr (.inl (.inl _)), kind => coinCost 108 kind
  | .inr (.inl (.inr (.inl query))), kind => RegistrationNativePublicationCosts.bill qSign query kind
  | .inr (.inl (.inr (.inr query))), kind => if effectKind query = kind then 1 else 0
  | .inr (.inr _), kind => coinCost qKem kind

theorem lifted_query (qSign qKem : Nat) (selected : Bool)
    (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill qSign qKem query kind)
      (RegistrationNativePublicFrontend.liftLocal selected query) (bill qSign qKem query kind) := by
  rcases query with message | (publication | kem)
  · simp [Weighted, RegistrationNativePublicFrontend.liftLocal, bill,
      RegistrationNativeRestrictedCosts.bill, isQueryBound_query_iff]
  · rcases publication with message | (publication | effect)
    all_goals simp [Weighted, RegistrationNativePublicFrontend.liftLocal, bill,
      RegistrationNativeRestrictedCosts.bill, isQueryBound_query_iff]
  · rcases kem with ordinary | (privateQuery | ciphertext)
    all_goals cases selected <;> simp [Weighted, RegistrationNativePublicFrontend.liftLocal,
      RegistrationNativeKemRouting.route, RegistrationNativePublicFrontend.liftRoutedKem,
      bill, RegistrationNativeRestrictedCosts.bill, isQueryBound_query_iff]

theorem lifted_program (qSign qKem : Nat) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (kind : EffectKind) (bound : Nat)
    (bounded : Weighted (fun query => bill qSign qKem query kind) work bound) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill qSign qKem query kind)
      (simulateQ (RegistrationNativePublicFrontend.liftLocal selected) work) bound :=
  weighted_simulate _ _ _ _ _ bounded (fun query => lifted_query qSign qKem selected query kind)

end BeaconcryptCore.Computational.RegistrationNativeReferenceCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReferenceCosts.lifted_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReferenceCosts.lifted_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReferenceCosts.lifted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReferenceCosts.lifted_program
