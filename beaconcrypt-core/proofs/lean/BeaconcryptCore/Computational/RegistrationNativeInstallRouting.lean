-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallTrace

/-! Actual native KEM routing and ordinary-owner preparation translation preserve the exact installation footprint. Neither introduces an installation from a preparation, KEM, or coin callback. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallRouting
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePublicFrontend (Spec LocalSpec liftLocal RoutedKem liftRoutedKem)
open RegistrationNativeInstallPredicate (LocalInstall GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem routed_free (role : Role) (work : OracleComp (RoutedKem KemSK) Value) :
    (simulateQ (liftRoutedKem (n := n)) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [liftRoutedKem, GlobalInstall, isQueryBoundP_query_iff]

private theorem local_step (role : Role) (selected : Bool) (query : (LocalSpec n KemSK).Domain) :
    (liftLocal selected query).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role)
      (if LocalInstall role query then 1 else 0) := by
  rcases query with message | (message | common) | kem
  · simp [liftLocal, GlobalInstall, LocalInstall, isQueryBoundP_query_iff]
  · simp [liftLocal, GlobalInstall, LocalInstall, isQueryBoundP_query_iff]
  · by_cases counted : Install role common <;>
      simp [liftLocal, GlobalInstall, LocalInstall, counted, isQueryBoundP_query_iff]
  · exact routed_free role _

/-- Literal actual local routing retains every role installation bill. -/
theorem local_bound (role : Role) (selected : Bool) (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count) :
    (simulateQ (liftLocal selected) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) count :=
  RawCtxSourceOpen.simulate_bound _ _ _ work count bounded (local_step role selected)

/-- Translating an ordinary owner's preparation preserves the same literal installation bill. -/
theorem ordinary_bound (role : Role) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativePublicOwners.ordinary, LocalInstall, ite_false]
      split <;> simp [LocalInstall, isQueryBoundP_query_iff]
  | inr query =>
      by_cases counted : LocalInstall (KemSK := KemSK) role (.inr query)
      · simp only [RegistrationNativePublicOwners.ordinary, isQueryBoundP_query_iff, ite_eq_left counted]
        intro _
        decide
      · simp only [RegistrationNativePublicOwners.ordinary, isQueryBoundP_query_iff, ite_eq_right counted]
        intro installed
        exact (counted installed).elim

end BeaconcryptCore.Computational.RegistrationNativeInstallRouting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRouting.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRouting.local_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRouting.ordinary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRouting.ordinary_bound
