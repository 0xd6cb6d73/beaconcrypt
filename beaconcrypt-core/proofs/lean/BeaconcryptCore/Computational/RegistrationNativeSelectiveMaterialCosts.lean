-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts

/-! The actual selective material service pays at most108 environment coin draws: selected inputs use the original44-byte material service, while nonselected protected inputs use their persistent108-byte output cache. Both branches make zero shared hashes and zero installation/administrative queries. Every failed preparation or capacity refusal remains in the literal stateful branch. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationNativePrimitiveCosts (coinCost coins_bound)
open RegistrationNativeSelectiveHiddenService (State onHidden known demand)
variable {n : Nat}

/-- The complete76+32-byte known output is sampled by its actual product sampler. -/
theorem output_bound : ($ᵗ PqxdhServerAuthKeySchedule.Output : ProbComp _).IsTotalQueryBound 108 := by
  rw [SampleableType.uniformSample_prod_eq_bind]
  exact isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) (fun left =>
      isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
        (fun right => show (pure (left, right) : ProbComp _).IsTotalQueryBound 0 from by trivial))

/-- Cached nonselected outputs cost zero; only a genuine cache miss uses the108-byte sampler. -/
theorem known_bound (bytes : Pqxdh.Bytes) (before : State n) (kind : EffectKind) :
    ((known bytes).run before).IsQueryBoundP (fun query => effectKind query = kind) (coinCost 108 kind) := by
  cases found : before.2 bytes with
  | some value => rw [RegistrationNativeSelectiveHiddenService.known_hit bytes before value found]; trivial
  | none =>
      rw [RegistrationNativeSelectiveHiddenService.known_miss bytes before found, isQueryBoundP_map_iff]
      exact coins_bound _ 108 output_bound kind

private theorem hidden_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : RegistrationNativeRelatedFamily.Message) (before : State n) (kind : EffectKind) :
    ((onHidden (RegistrationNativeHiddenService.demand source input inside message)).run before).IsQueryBoundP
      (fun query => effectKind query = kind) (coinCost 108 kind) := by
  simp only [onHidden, StateT.run, isQueryBoundP_map_iff]
  cases kind with
  | coin =>
      apply OracleComp.IsQueryBoundP.mono _ (by decide : 44 ≤ 108)
      exact OracleComp.IsQueryBoundP.of_imp (fun _ _ => trivial)
        ((isQueryBoundP_true_iff _ _).mpr (RegistrationNativeHiddenServiceBounds.demand_bound source input inside message before.1))
  | hash =>
      apply OracleComp.IsQueryBoundP.of_imp _ (RegistrationNativeHiddenServiceBounds.demand_free source input inside message before.1)
      intro query matching
      cases query with
      | inl coin => cases matching
      | inr query => trivial
  | administrative =>
      apply OracleComp.IsQueryBoundP.of_imp _ (RegistrationNativeHiddenServiceBounds.demand_free source input inside message before.1)
      intro query matching
      cases query with
      | inl coin => cases matching
      | inr query => trivial

attribute [local irreducible] RegistrationNativeHiddenService.demand

/-- All actual selected/ordinary/off-protected/failure histories satisfy the same literal effect bill. -/
theorem demand_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : RegistrationNativeRelatedFamily.Message)
    (before : State n) (kind : EffectKind) :
    ((demand source input inside candidate message).run before).IsQueryBoundP
      (fun query => effectKind query = kind) (coinCost 108 kind) := by
  simp only [demand, StateT.run]
  split
  · cases realized : input message with
    | none => exact hidden_bound source input _ message before kind
    | some bytes =>
        simp only []
        split
        · rw [isQueryBoundP_map_iff]
          exact known_bound bytes _ kind
        · exact hidden_bound source input _ message before kind
  · exact hidden_bound source input _ message before kind

end BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts.output_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts.output_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts.known_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts.known_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts.demand_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts.demand_bound
