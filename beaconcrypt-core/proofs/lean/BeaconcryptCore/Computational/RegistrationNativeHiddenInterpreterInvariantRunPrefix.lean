-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRun

/-! A literal supported query prefix retains its exact remaining demand allowance. Applying this source-tree receipt to the actual whole native run derives capacity before every reached material demand from the original build-plus-finish budget. No external invariant, scan interpreter or whole-program cap is supplied to the concrete endpoints. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (State Provider handler initial)
open RegistrationNativeHiddenInterpreterInvariant (Good query_good query_count)
open RegistrationNativePublicCaps (IsDemand)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- A concrete query-tree prefix records actual supported callbacks and the exact suspended continuation. -/
inductive Prefix
    (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (State n KemSK ProviderState) (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))) :
    OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value → State n KemSK ProviderState →
      OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value → State n KemSK ProviderState → Prop where
  | refl (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (state : State n KemSK ProviderState) :
      Prefix implementation work state work state
  | step (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
      (next : (RegistrationNativePublicFrontend.Spec n KemSK).Range query → OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
      (before : State n KemSK ProviderState) (reply : (RegistrationNativePublicFrontend.Spec n KemSK).Range query)
      (middle : State n KemSK ProviderState) (residual : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
      (after : State n KemSK ProviderState)
      (supported : (reply, middle) ∈ support ((implementation query).run before))
      (later : Prefix implementation (next reply) middle residual after) :
      Prefix implementation (((RegistrationNativePublicFrontend.Spec n KemSK).query query : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) ((RegistrationNativePublicFrontend.Spec n KemSK).Range query)) >>= next) before residual after

/-- The actual allocator counts the consumed prefix and retains a structural allowance for precisely its suspended continuation. -/
theorem prefix_budget (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (work residual : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before after : State n KemSK ProviderState)
    (reached : Prefix (handler setup wire sign seed scalar provider) work before residual after)
    (count : Nat) (bounded : work.IsQueryBoundP (IsDemand (KemSK := KemSK)) count) (good : Good before) :
    Good after ∧ ∃ remaining, after.keys.demands + remaining ≤ before.keys.demands + count ∧
      residual.IsQueryBoundP (IsDemand (KemSK := KemSK)) remaining := by
  induction reached generalizing count with
  | refl work before => exact ⟨good, count, le_refl _, bounded⟩
  | step query next before reply middle residual after supported later ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have middleGood := query_good setup wire sign seed scalar provider query before (reply, middle) good supported
      obtain ⟨afterGood, remaining, credit, tail⟩ := ih _ (bounded.2 reply) middleGood
      have spent := query_count setup wire sign seed scalar provider query before (reply, middle) good supported
      refine ⟨afterGood, remaining, ?_, tail⟩
      by_cases counted : IsDemand (KemSK := KemSK) query
      · have positive : 0 < count := bounded.1.resolve_left (not_not.mpr counted)
        simp only [ite_eq_left counted] at credit spent
        omega
      · simp only [ite_eq_right counted] at credit spent
        omega

/-- Every reached prefix of the literal initialized native run derives its remaining demand allowance from the original CE budget. -/
theorem run_prefix_budget (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (frontend : RegistrationNativePublicFrontend.State source)
    (residual : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)
      (RegistrationNativeHiddenInterpreterInvariantRun.Outcome Value source)) (after : State n KemSK ProviderState)
    (reached : Prefix (handler setup wire (RegistrationNativeMldsa.owned source credential) seed scalar provider)
      (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work frontend)
      (initial providerState) residual after) :
    Good after ∧ ∃ remaining, after.keys.demands + remaining ≤ budget.cap 4 + budget.cap 5 ∧
      residual.IsQueryBoundP (IsDemand (KemSK := KemSK)) remaining := by
  have actual := prefix_budget setup wire (RegistrationNativeMldsa.owned source credential) seed scalar provider _ residual
    (initial providerState) after reached (budget.cap 4 + budget.cap 5)
    (RegistrationNativePublicCaps.run_bound setup checks wire source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work budget bounded frontend)
    (RegistrationNativeHiddenInterpreterInvariant.initial_good providerState)
  simpa only [initial, RegistrationNativeHiddenService.initial, Nat.zero_add] using actual

/-- Before every reached actual material demand, the original public budget supplies room for its genuine allocator, including literal aliases. -/
theorem run_prefix_capacity (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (capacity : budget.cap 4 + budget.cap 5 ≤ n) (frontend : RegistrationNativePublicFrontend.State source)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (next : (RegistrationNativePublicFrontend.Spec n KemSK).Range query →
      OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) (RegistrationNativeHiddenInterpreterInvariantRun.Outcome Value source))
    (after : State n KemSK ProviderState)
    (reached : Prefix (handler setup wire (RegistrationNativeMldsa.owned source credential) seed scalar provider)
      (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work frontend)
      (initial providerState) (((RegistrationNativePublicFrontend.Spec n KemSK).query query : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) ((RegistrationNativePublicFrontend.Spec n KemSK).Range query)) >>= next) after)
    (counted : IsDemand (KemSK := KemSK) query) :
    Good after ∧ after.keys.demands < n ∧ ∀ bytes, ∃ slot,
      (RegistrationNativeHiddenService.reserve bytes { after.keys with demands := after.keys.demands + 1 }).1 = some slot := by
  obtain ⟨good, remaining, credit, residual⟩ := run_prefix_budget setup checks wire credential seed scalar provider providerState
    selectedOwner selectedAccept serverKeyId bounds mode work budget bounded frontend _ after reached
  rw [isQueryBoundP_query_bind_iff] at residual
  have positive : 0 < remaining := residual.1.resolve_left (not_not.mpr counted)
  have room : after.keys.demands < n := by omega
  exact ⟨good, room, fun bytes => RegistrationNativeHiddenServiceInvariant.reserve_some bytes after.keys good.1 room⟩

end BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix.prefix_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix.prefix_budget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix.run_prefix_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix.run_prefix_budget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix.run_prefix_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariantRunPrefix.run_prefix_capacity
