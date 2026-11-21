-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore
/-! The actual physical recovery client inherits both ordinary oracle bills from the original Word material-demand allowance. Its persistent World interpreter contributes only local probability coins; all private source, opaque-root and physical state is retained through the literal trace observer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativePlatformRecordPartnerExposureClient (Shared Private ambient implementationWith programWith client)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}

private theorem coins_free (kind : Kind) (work : ProbComp A) :
    (simulateQ RegistrationNativeSecretWordService.coins work).IsQueryBoundP (Counted kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _=>False) _ _ 0 (isQueryBoundP_false work 0)
  intro query
  cases kind <;> simp [RegistrationNativeSecretWordService.coins,Counted,
    RegistrationNativeSecretWordRecoveryCompiler.IsKey,RegistrationNativeSecretWordRecoveryCompiler.IsSuffix,
    RegistrationNativeSecretWord.IsKey,isQueryBoundP_query_iff]

/-- Every actual ambient query has the same counted Combined class; physical execution introduces no recovery oracle request. -/
theorem ambient_bound (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (query : (Shared n).Domain) (before : Physical) (kind : Kind) :
    ((ambient physical query).run before).IsQueryBoundP (Counted kind)
      (if RegistrationNativePlatformRecordPartnerExposureRootCaps.Counted (n := n) kind query then 1 else 0) := by
  cases query with
  | inl query=>
    by_cases counted : Counted kind query <;>
      simp [ambient,StateT.run_lift,bind_pure_comp,isQueryBoundP_map_iff,isQueryBoundP_query_iff,
        RegistrationNativePlatformRecordPartnerExposureRootCaps.Counted,counted]
  | inr query=>
    simp only [ambient,StateT.run,RegistrationNativePlatformRecordPartnerExposureRootCaps.Counted,ite_false]
    exact coins_free kind _

/-- Closing arbitrary actual physical World continuations preserves the existing combined allowance. -/
theorem ambient_program_bound (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (work : OracleComp (Shared n) A) (cap : Nat) (kind : Kind)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformRecordPartnerExposureRootCaps.Counted kind) cap) (before : Physical) :
    ((simulateQ (ambient physical) work).run before).IsQueryBoundP (Counted kind) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using ambient_bound physical query current kind
  · intro query free current
    simpa only [ite_eq_right free] using ambient_bound physical query current kind

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))

/-- The complete source/private/physical implementation charges at most one query of either class exactly at material demand. -/
theorem implementation_bound (operand : RegistrationNativeSecretWordMessage.Message →RegistrationNativeSecretWordMessage.Message)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) (before : Private n KemSK Physical) (kind : Kind) :
    ((implementationWith setup wire sign seed scalar provider physical operand query).run before).IsQueryBoundP (Counted kind)
      (if RegistrationNativeSecretWordInterpreterCaps.IsDemand (n := n) (KemSK := KemSK) query then 1 else 0) := by
  rw [implementationWith,QueryImpl.flattenStateT_mapStateTBase_apply_run,isQueryBoundP_map_iff]
  exact ambient_program_bound physical _ _ kind
    (RegistrationNativePlatformRecordPartnerExposureClientCapsCore.lower_bound setup wire sign seed scalar provider operand query before.1 kind) before.2

/-- Any adaptive Word execution retains both recovery bills from its literal material-demand cap. -/
theorem execution_bound (operand : RegistrationNativeSecretWordMessage.Message →RegistrationNativeSecretWordMessage.Message)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordInterpreterCaps.IsDemand (n := n) (KemSK := KemSK)) cap)
    (before : Private n KemSK Physical) (kind : Kind) :
    ((simulateQ (implementationWith setup wire sign seed scalar provider physical operand) work).run before).IsQueryBoundP (Counted kind) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using implementation_bound setup wire sign seed scalar provider physical operand query current kind
  · intro query free current
    simpa only [ite_eq_right free] using implementation_bound setup wire sign seed scalar provider physical operand query current kind

/-- The literal private trace observer adds no recovery requests, for any analysis demand operand. -/
theorem program_bound (operand : RegistrationNativeSecretWordMessage.Message →RegistrationNativeSecretWordMessage.Message)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordInterpreterCaps.IsDemand (n := n) (KemSK := KemSK)) cap)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : Private n KemSK Physical) (kind : Kind) :
    (programWith setup wire sign seed scalar provider physical operand work trace before).IsQueryBoundP (Counted kind) cap := by
  exact execution_bound setup wire sign seed scalar provider physical operand _ cap
    (RegistrationNativeSecretWordFrontendTrace.program_bound _ work cap bounded trace) before kind

/-- The executable candidate-independent recovery client receives exactly the original material allowance for both oracle classes. -/
theorem client_bound (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordInterpreterCaps.IsDemand (n := n) (KemSK := KemSK)) cap)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : Private n KemSK Physical) (kind : Kind) :
    (client setup wire sign seed scalar provider physical work trace before).IsQueryBoundP (Counted kind) cap :=
  program_bound setup wire sign seed scalar provider physical id work cap bounded trace before kind
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.ambient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.ambient_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.ambient_program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.ambient_program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.implementation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.implementation_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.execution_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.execution_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps.client_bound
