-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup
import BeaconcryptCore.Computational.RegistrationNativePublicCaps

/-! Keeping the opaque KEM interface open adds no material requests. The actual retained, preparation and key compilers preserve the original build-plus-finish material bill; generated startup and independent challenge generation add none. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsDemand : (RegistrationNativeOpenRetained.Spec KemSK).Domain → Prop
  | .inl query => RegistrationNativeRetainedService.IsDemand query
  | .inr _ => False

def IsPhaseDemand : (RegistrationNativeOpenKey.PhaseSpec KemSK).Domain → Prop
  | .inl query => RegistrationNativeKeyBounds.IsDemand query
  | .inr _ => False

def IsMaterial : (RegistrationNativeOpenKey.Spec KemSK).Domain → Prop
  | .inl query => (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output)) query
  | .inr _ => False

instance : DecidablePred (IsDemand (KemSK := KemSK)) := fun query => by
  cases query with
  | inl query => exact inferInstanceAs (Decidable (RegistrationNativeRetainedService.IsDemand query))
  | inr _ => exact isFalse id
instance : DecidablePred (IsPhaseDemand (KemSK := KemSK)) := fun query => by
  cases query with
  | inl query => exact inferInstanceAs (Decidable (RegistrationNativeKeyBounds.IsDemand query))
  | inr _ => exact isFalse id
instance : DecidablePred (IsMaterial (KemSK := KemSK)) := fun query => by
  cases query with
  | inl query => exact inferInstanceAs (Decidable ((PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output)) query))
  | inr _ => exact isFalse id

local notation "Demand" => IsDemand (KemSK := KemSK)
local notation "PhaseDemand" => IsPhaseDemand (KemSK := KemSK)
local notation "Material" => IsMaterial (KemSK := KemSK)

private theorem base_bound (work : OracleComp RegistrationNativeRetainedService.Spec Value) (count : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativeRetainedService.IsDemand count) :
    (simulateQ (RegistrationNativeOpenRetained.baseLift (KemSK := KemSK)) work).IsQueryBoundP Demand count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  simp only [RegistrationNativeOpenRetained.baseLift, IsDemand, isQueryBoundP_query_iff]
  intro counted
  simpa only [ite_eq_left counted] using Nat.zero_lt_one

private theorem ordinary_free (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    ((RegistrationNativeOpenRetained.ordinary hmac work).run before).IsQueryBoundP Demand 0 := by
  simp only [RegistrationNativeOpenRetained.ordinary, StateT.run, isQueryBoundP_map_iff]
  apply base_bound
  unfold RegistrationNativePublicRetained.ordinary
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]

private theorem retained_step (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    ((RegistrationNativeOpenRetained.compiler setup wire route sign query).run before).IsQueryBoundP Demand
      (if RegistrationNativePublicCaps.IsDemand (KemSK := KemSK) query then 1 else 0) := by
  rcases query with (message | (message | query) | query) | query
  · simp [RegistrationNativeOpenRetained.compiler, RegistrationNativeOpenRetained.baseLift, StateT.run_lift,
      bind_pure_comp, isQueryBoundP_map_iff, IsDemand, RegistrationNativeRetainedService.IsDemand,
      RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]
  · simp [RegistrationNativeOpenRetained.compiler, RegistrationNativeOpenRetained.baseLift, StateT.run_lift,
      bind_pure_comp, isQueryBoundP_map_iff, IsDemand, RegistrationNativeRetainedService.IsDemand,
      RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]
  · exact ordinary_free _ _ before
  · simp [RegistrationNativeOpenRetained.compiler, RegistrationNativeOpenRetained.kemLift,
      StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, IsDemand,
      RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]
  · exact ordinary_free _ _ before

/-- The open retained client preserves the original material allowance through all opaque KEM callbacks. -/
theorem retained_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : RegistrationNativePublicInterpreter.State n KemSK)
    (count : Nat) (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) count) :
    (RegistrationNativeOpenRetained.client setup wire route sign work before).IsQueryBoundP Demand count := by
  unfold RegistrationNativeOpenRetained.client
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using retained_step setup wire route sign query current
  · intro query free current
    simpa only [ite_eq_right free] using retained_step setup wire route sign query current

private theorem phase_lift_bound (work : OracleComp RegistrationNativeKeyPhases.Spec Value) (count : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativeKeyBounds.IsDemand count) :
    (simulateQ (RegistrationNativeOpenKey.phaseLift (KemSK := KemSK)) work).IsQueryBoundP PhaseDemand count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  simp only [RegistrationNativeOpenKey.phaseLift, IsPhaseDemand, isQueryBoundP_query_iff]
  intro counted
  simpa only [ite_eq_left counted] using Nat.zero_lt_one

/-- Preparation flags do not turn an external KEM request into a material demand. -/
theorem phase_bound (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP Demand count) :
    (RegistrationNativeOpenKey.phaseClient work).IsQueryBoundP PhaseDemand count := by
  unfold RegistrationNativeOpenKey.phaseClient
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted before
    cases query with
    | inl query =>
        change RegistrationNativeRetainedService.IsDemand query at counted
        exact phase_lift_bound _ 1 (by simpa only [ite_eq_left counted] using RegistrationNativeRetainedService.compiler_bound query before)
    | inr query => exact False.elim counted
  · intro query free before
    cases query with
    | inl query =>
        change ¬ RegistrationNativeRetainedService.IsDemand query at free
        exact phase_lift_bound _ 0 (by simpa only [ite_eq_right free] using RegistrationNativeRetainedService.compiler_bound query before)
    | inr query =>
        simp [RegistrationNativeOpenKey.phaseCompiler, StateT.run_lift, bind_pure_comp,
          IsPhaseDemand, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem key_lift_bound (work : OracleComp RegistrationNativeKeyHybrid.Spec Value) (count : Nat)
    (bounded : work.IsQueryBoundP (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output)) count) :
    (simulateQ (RegistrationNativeOpenKey.keyLift (KemSK := KemSK)) work).IsQueryBoundP Material count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  simp only [RegistrationNativeOpenKey.keyLift, IsMaterial, isQueryBoundP_query_iff]
  intro counted
  simpa only [ite_eq_left counted] using Nat.zero_lt_one

/-- The open key compiler makes at most one protected table query per original material demand. -/
theorem key_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP Demand count) :
    (RegistrationNativeOpenKey.client source input inside work).IsQueryBoundP Material count := by
  unfold RegistrationNativeOpenKey.client
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply (phase_bound work count bounded).simulateQ_run_of_step
  · intro query counted before
    cases query with
    | inl query =>
        cases query with
        | inl coin => exact False.elim counted
        | inr request => cases request with
          | prepare message => exact False.elim counted
          | demand message => exact key_lift_bound _ 1 (RegistrationNativeKeyBounds.compiler_demand source input inside message before)
    | inr query => exact False.elim counted
  · intro query free before
    cases query with
    | inl query => exact key_lift_bound _ 0 (RegistrationNativeKeyBounds.compiler_free source input inside query free before)
    | inr query =>
        simp [RegistrationNativeOpenKey.keyCompiler, StateT.run_lift, bind_pure_comp,
          IsMaterial, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps.retained_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps.phase_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps.phase_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps.key_bound
