-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariant

/-! Arbitrary adaptive native frontend interleavings preserve the actual thin allocator and obey their original material-demand query cap. These statements concern supported concrete interpreter runs, including every failure branch and arbitrary external World/KEM behavior. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantProgram
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSelectiveHiddenInterpreter (State handler)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreterInvariant (Good query_good query_count)
open RegistrationNativePublicCaps (IsDemand)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

/-- Every actual adaptive native continuation preserves the derived ordered injective slot allocation. -/
theorem program_good (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) (result : Value × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((simulateQ (handler setup wire sign seed scalar candidate provider) work).run before)) :
    Good result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact good
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, stepped, continued⟩ := supported
      exact ih middle.1 middle.2 (query_good setup wire sign seed scalar candidate provider query before middle good stepped) continued

/-- The actual reached thin demand count is bounded by the original classwise query allowance. -/
theorem program_count (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (IsDemand (KemSK := KemSK)) count)
    (before : State n KemSK ProviderState) (result : Value × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((simulateQ (handler setup wire sign seed scalar candidate provider) work).run before)) :
    result.2.1.keys.demands ≤ before.1.keys.demands + count := by
  induction work using OracleComp.inductionOn generalizing count before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      change before.1.keys.demands ≤ before.1.keys.demands + count
      omega
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, stepped, continued⟩ := supported
      have valid := query_good setup wire sign seed scalar candidate provider query before middle good stepped
      have tail := ih middle.1 _ (bounded.2 middle.1) _ valid continued
      have head := query_count setup wire sign seed scalar candidate provider query before middle good stepped
      by_cases counted : IsDemand (KemSK := KemSK) query
      · have positive : 0 < count := bounded.1.resolve_left (not_not.mpr counted)
        simp only [ite_eq_left counted] at tail head
        omega
      · simp only [ite_eq_right counted] at tail head
        omega

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantProgram.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantProgram.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantProgram.program_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreterInvariantProgram.program_count
