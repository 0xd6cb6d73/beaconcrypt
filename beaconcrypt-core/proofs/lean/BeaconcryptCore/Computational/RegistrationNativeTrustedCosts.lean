-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWeightedContext

/-! Literal weighted bills for the original Beacon constructor/outgoing primitive surface and its unchanged public-reference embedding. No private material or callback outcome is supplied to these costs. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeTrustedCosts
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationNativePrimitiveCosts (coinCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono weighted_run weighted_simulate)
open RegistrationNativeWeightedContext (query_bound map_bound probability_bound)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

def bill (qKem : Nat) (kind : EffectKind) : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain → Nat
  | .inl query => if effectKind query = kind then 1 else 0
  | .inr _ => coinCost qKem kind

/-- Existing effect injection retains its literal one-query cost. -/
theorem effect_bound (source : RegistrationNativeMldsa.Source) (qKem : Nat) (kind : EffectKind)
    (query : (EnvEffects n).Domain) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK) query).run owners).run env)
      (if effectKind query = kind then 1 else 0) := by
  simp only [RegistrationNativeBeaconFrontend.effect, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact map_bound _ _ _ _ (query_bound _ _)

/-- An original source probability sampler retains both state coordinates and its exact draw bill. -/
theorem sample_bound (source : RegistrationNativeMldsa.Source) (qKem : Nat) (kind : EffectKind)
    (work : ProbComp Value) (count : Nat) (bounded : work.IsTotalQueryBound count)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) work).run owners).run env)
      (coinCost count kind) := by
  have weighted := probability_bound (fun _ => coinCost 1 kind) (coinCost 1 kind) (fun _ => rfl) work count bounded
  have interpreted := RegistrationNativeWeightedContext.run_bound (fun _ => coinCost 1 kind) (bill (n := n) qKem kind)
    (fun query => RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK) (.inl query)) work _ owners env weighted
    (fun query current environment => by
      cases kind <;> exact effect_bound source qKem _ (.inl query) current environment)
  cases kind <;> simpa only [RegistrationNativeBeaconFrontend.sample, coinCost, Nat.one_mul, Nat.zero_mul] using interpreted

/-- Typed KEM routing preserves its actual one-request primitive bill. -/
theorem kem_bound (source : RegistrationNativeMldsa.Source) (qKem : Nat) (kind : EffectKind)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.kem (n := n) query).run owners).run env) (coinCost qKem kind) := by
  simp only [RegistrationNativeBeaconFrontend.kem, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact map_bound _ _ _ _ (query_bound _ _)

/-- The existing native trusted request embedding forwards effects and routed KEM with unchanged bills. -/
theorem embedded_query (qSign qKem : Nat) (kind : EffectKind)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill qSign qKem query kind)
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false) (RegistrationBeaconReferenceCompiler.trustedLift query))
      (bill qKem kind query) := by
  rcases query with query | (query | (query | key))
  all_goals simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
    RegistrationBeaconReferenceCompiler.indexed, RegistrationNativePublicFrontend.liftLocal,
    RegistrationNativePublicFrontend.liftRoutedKem, RegistrationNativeKemRouting.route,
    Bool.false_eq_true, ite_false, simulateQ_spec_query]
  all_goals exact query_bound _ _

/-- The whole actual trusted program retains its source bill through public owner/reference embedding. -/
theorem embedded_program (qSign qKem : Nat) (kind : EffectKind)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (count : Nat)
    (bounded : Weighted (bill (n := n) qKem kind) work count) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill qSign qKem query kind)
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false) (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work)) count := by
  rw [← QueryImpl.simulateQ_compose]
  exact weighted_simulate _ _ _ work count bounded (embedded_query qSign qKem kind)

end BeaconcryptCore.Computational.RegistrationNativeTrustedCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.effect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.effect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.sample_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.sample_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.kem_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.kem_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.embedded_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.embedded_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.embedded_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTrustedCosts.embedded_program
