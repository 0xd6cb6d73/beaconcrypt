-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler

/-! Actual compiled common services mutate signing receipts while retaining the unrelated record-request marker field. The proof follows the current mutable environment, rather than inferring this property from a projected source equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase
open RegistrationWorldAgreementCompiler (EnvState)
variable {κ ι Auxiliary Value Next : Type} {spec : OracleSpec κ} {target : OracleSpec ι} {n : Nat}

def Keeps (work : StateT (EnvState Auxiliary) (OracleComp target) Value) : Prop :=
  ∀ env result, result ∈ support (work.run env) → result.2.recordRequests = env.recordRequests

theorem pure_keeps (value : Value) : Keeps (pure value : StateT (EnvState Auxiliary) (OracleComp target) Value) := by
  intro env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

theorem bind_keeps (work : StateT (EnvState Auxiliary) (OracleComp target) Value)
    (next : Value → StateT (EnvState Auxiliary) (OracleComp target) Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1 middle.2 result continued).trans (first env middle reached)

theorem lift_keeps (work : OracleComp target Value) :
    Keeps (StateT.lift work : StateT (EnvState Auxiliary) (OracleComp target) Value) := by
  intro env result supported
  simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨value, _, rfl⟩ := supported
  rfl

theorem program_keeps (implementation : QueryImpl spec (StateT (EnvState Auxiliary) (OracleComp target)))
    (step : ∀ query, Keeps (implementation query)) (work : OracleComp spec Value) :
    Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (step query) ih

theorem forward_support (implementation : QueryImpl spec (OracleComp target))
    (work : OracleComp spec Value) (value : Value) (supported : value ∈ support (simulateQ implementation work)) :
    value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure output => exact supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, by simp, ih reply continued⟩

/-- Every actual common-service query retains all record-request markers while appending any real signing receipt to its separate field. -/
theorem service_keeps (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (OracleComp target))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.PublicSpec n).Domain) :
    Keeps (RegistrationNativeCommonCompiler.service (Auxiliary := Auxiliary) environment demand hkdf writer sign query) := by
  intro env result supported
  cases query with
  | inl message => exact lift_keeps _ env result supported
  | inr query => cases query with
    | inl query =>
        simp only [RegistrationNativeCommonCompiler.service, RegistrationNativeCommonCompiler.common,
          RegistrationNativeCommonCompiler.publication, StateT.run, support_map] at supported
        obtain ⟨inner, _, rfl⟩ := supported
        rfl
    | inr query => exact lift_keeps _ env result supported

/-- Full current-environment material components retain record markers through arbitrary native failures and signing outcomes. -/
theorem service_program (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (OracleComp target))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    Keeps (simulateQ (RegistrationNativeCommonCompiler.service (Auxiliary := Auxiliary) environment demand hkdf writer sign) work) :=
  program_keeps _ (service_keeps environment demand hkdf writer sign) work

end BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.pure_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.pure_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.bind_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.bind_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.lift_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.lift_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.forward_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.forward_support
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.service_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.service_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.service_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase.service_program
