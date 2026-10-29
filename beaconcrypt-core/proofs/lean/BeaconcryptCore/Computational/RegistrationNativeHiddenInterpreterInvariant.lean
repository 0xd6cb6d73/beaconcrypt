-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativePublicCaps

/-! The actual thin native interpreter preserves its literal-address allocator invariants and counts exactly its material-demand callbacks. Arbitrary KEM providers, chronological signing receipts and World replies are retained. No validity property of an external interpreter is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (State Provider handler onKeys initial)
open RegistrationNativeHiddenServiceInvariant (Ordered InjectiveSlots)
open RegistrationNativePublicCaps (IsDemand)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def Good (before : State n KemSK ProviderState) : Prop := Ordered before.keys ∧ InjectiveSlots before.keys

/-- The literal empty thin service starts with an ordered injective address allocation. -/
theorem initial_good (providerState : ProviderState) : Good (initial (n := n) (KemSK := KemSK) providerState) :=
  RegistrationNativeHiddenServiceInvariant.initial

private theorem keys_support (work : StateT (RegistrationNativeHiddenService.State n)
    (OracleComp (PqxdhRecordLiftInterface.EnvEffects n)) Value) (before : State n KemSK ProviderState)
    (result : Value × State n KemSK ProviderState) (supported : result ∈ support ((onKeys work).run before)) :
    ∃ inner, inner ∈ support (work.run before.keys) ∧ result.1 = inner.1 ∧ result.2.keys = inner.2 := by
  simp only [onKeys, StateT.run, support_map] at supported
  obtain ⟨inner, actual, rfl⟩ := supported
  exact ⟨inner, PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ actual, rfl, rfl⟩

private theorem query_step (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar provider query).run before)) :
    result.2.keys.demands = before.keys.demands + (if IsDemand query then 1 else 0) ∧ Good result.2 := by
  rcases query with (message | (message | query) | query) | query
  · obtain ⟨inner, actual, _reply, after⟩ := keys_support _ before result supported
    have invariant := RegistrationNativeHiddenServiceInvariant.prepare_keeps _ _ before.keys inner.2 inner.1 good.1 good.2 actual
    dsimp only [RegistrationNativeHiddenService.prepare, StateT.run] at actual
    rw [mem_support_pure_iff] at actual
    cases actual
    exact ⟨by simp only [after, IsDemand, ite_false, Nat.add_zero], by simpa only [Good, after] using invariant⟩
  · obtain ⟨inner, actual, _reply, after⟩ := keys_support _ before result supported
    have invariant := RegistrationNativeHiddenServiceDemand.demand_keeps _ _ _ _ before.keys inner.2 inner.1 good.1 good.2 actual
    exact ⟨by simpa only [after, IsDemand, ite_true] using invariant.1, by simpa only [Good, after] using invariant.2⟩
  · cases query with
    | inl publication =>
        simp only [handler, RegistrationNativeHiddenInterpreter.publication, StateT.run, support_map] at supported
        obtain ⟨inner, _actual, rfl⟩ := supported
        exact ⟨rfl, good⟩
    | inr effect =>
        simp only [handler, RegistrationNativeHiddenInterpreter.effect, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨inner, _actual, rfl⟩ := supported
        exact ⟨rfl, good⟩
  · simp only [handler, RegistrationNativeHiddenInterpreter.routed, StateT.run, support_map] at supported
    obtain ⟨inner, _actual, rfl⟩ := supported
    exact ⟨rfl, good⟩
  · simp only [handler, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨inner, _actual, rfl⟩ := supported
    exact ⟨rfl, good⟩

/-- Every supported actual native callback preserves ordered injective full-input allocation. -/
theorem query_good (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar provider query).run before)) :
    Good result.2 := (query_step setup wire sign seed scalar provider query before result good supported).2

/-- Only a material-demand callback increments the actual thin demand counter, exactly once on every failure or success branch. -/
theorem query_count (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar provider query).run before)) :
    result.2.keys.demands = before.keys.demands + (if IsDemand query then 1 else 0) :=
  (query_step setup wire sign seed scalar provider query before result good supported).1

end BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant.initial_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant.initial_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant.query_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant.query_count
