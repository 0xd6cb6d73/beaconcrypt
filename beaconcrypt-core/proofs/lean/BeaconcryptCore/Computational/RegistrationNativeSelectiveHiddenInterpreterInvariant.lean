-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant

/-! The actual selective interpreter retains the original ordered injective material-slot allocator and counts every demand exactly once. The nonselected108-byte cache remains in the reached state and no invariant of an external callback interpreter is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSelectiveHiddenInterpreter (State handler onKeys onBase initial)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePublicCaps (IsDemand)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def Good (before : State n KemSK ProviderState) : Prop := RegistrationNativeHiddenInterpreterInvariant.Good before.1

/-- Empty initialization supplies the actual ordered injective selective allocator. -/
theorem initial_good (providerState : ProviderState) : Good (initial (n := n) (KemSK := KemSK) providerState) :=
  RegistrationNativeHiddenInterpreterInvariant.initial_good providerState

private theorem other_step (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (other : ¬IsDemand query)
    (before : State n KemSK ProviderState) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar candidate provider query).run before)) :
    result.2.1.keys.demands = before.1.keys.demands + (if IsDemand query then 1 else 0) ∧ Good result.2 := by
  rw [RegistrationNativeSelectiveHiddenInterpreter.query_other setup wire sign seed scalar candidate provider query other] at supported
  simp only [onBase, StateT.run, support_map] at supported
  obtain ⟨inner, actual, rfl⟩ := supported
  exact ⟨RegistrationNativeHiddenInterpreterInvariant.query_count setup wire sign seed scalar provider query before.1 inner good actual,
    RegistrationNativeHiddenInterpreterInvariant.query_good setup wire sign seed scalar provider query before.1 inner good actual⟩

private theorem query_step (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar candidate provider query).run before)) :
    result.2.1.keys.demands = before.1.keys.demands + (if IsDemand query then 1 else 0) ∧ Good result.2 := by
  rcases query with (message | (message | common) | kem) | record
  all_goals try exact other_step setup wire sign seed scalar candidate provider _ (by intro impossible; exact impossible) before result good supported
  simp only [handler, onKeys, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  have kept := RegistrationNativeSelectiveHiddenServiceInvariant.demand_keeps setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    candidate message (before.1.keys, before.2) inner.2 inner.1 good.1 good.2 actual
  exact ⟨by simpa only [IsDemand, ite_true] using kept.1, kept.2⟩

/-- Every actual selective callback preserves the ordered injective allocator in its full reached private state. -/
theorem query_good (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar candidate provider query).run before)) :
    Good result.2 := (query_step setup wire sign seed scalar candidate provider query before result good supported).2

/-- Exactly one demand is charged on every selected-hidden, nonselected-known or failure branch; other callbacks charge none. -/
theorem query_count (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar candidate provider query).run before)) :
    result.2.1.keys.demands = before.1.keys.demands + (if IsDemand query then 1 else 0) :=
  (query_step setup wire sign seed scalar candidate provider query before result good supported).1

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant.initial_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant.initial_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant.query_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant.query_count
