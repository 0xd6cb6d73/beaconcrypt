-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld

/-! A successful actual selective material reply certifies that the descriptor's native full input exists. Invalid-input vacuity cannot supply a successful installation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveDemandRealized
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

/-- The original executing material callback cannot return a choice at an invalid native descriptor. -/
theorem source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (message : RegistrationNativeRelatedFamily.Message)
    (before after : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (choice : RegistrationNativePairedChoice.Choice n)
    (supported : (some choice, after) ∈ support
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
        (.inl (.inr (.inl (.inl message))))).run before)) :
    ∃ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes := by
  rw [RegistrationNativeSelectiveHiddenInterpreter.query_demand] at supported
  simp only [RegistrationNativeSelectiveHiddenInterpreter.onKeys, StateT.run, support_map] at supported
  obtain ⟨result, possible, returned⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset PqxdhRecordLiftInterface.effectLift _ possible
  have chosen : result.1 = some choice := congrArg Prod.fst returned
  cases realized : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message with
  | some bytes => exact ⟨bytes, rfl⟩
  | none =>
      by_cases prepared : before.1.keys.prepared message = true
      · simp only [RegistrationNativeSelectiveHiddenService.demand, StateT.run, prepared, ite_true,
          RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
          realized, map_pure, mem_support_pure_iff] at original
        subst result
        cases chosen
      · simp only [RegistrationNativeSelectiveHiddenService.demand, StateT.run, ite_eq_right prepared,
          RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
          map_pure, mem_support_pure_iff] at original
        subst result
        cases chosen

end BeaconcryptCore.Computational.RegistrationNativeSelectiveDemandRealized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveDemandRealized.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveDemandRealized.source
