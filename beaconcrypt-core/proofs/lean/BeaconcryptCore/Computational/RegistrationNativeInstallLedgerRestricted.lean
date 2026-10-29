-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerInterface

/-! The original secrecy controller issues only coins and record sends. Such actual callback programs retain all successful installation messages and forward all physical hidden slots, including when the eventual send is refused. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallLedger
open RegistrationNativeInstallOrdinals (messages handles)
open RegistrationNativeInstallStep (RoleStep)
variable {n : Nat} {NativeState Value : Type}
variable (native : QueryImpl RegistrationNativeInterface.Spec (StateT NativeState ProbComp))
    (events : NativeState → List RegistrationNativeG2Trace.Event)
    (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (valid : NativeState → Prop) (selected : RegistrationNativeRelatedFamily.Message → Prop)
    (storage : ∀ query before result, valid before → result ∈ support ((native query).run before) →
      Storage slots valid before result.2)
    (rawStep : ∀ query before result, valid before → result ∈ support ((native query).run before) →
      ∀ role, RoleStep role (events before) (events result.2) ⟨.inl query, result.1⟩ (slots result.2) selected)

private theorem restricted_handles (query : RegistrationNativeInterface.Spec.Domain)
    (reply : RegistrationNativeInterface.Spec.Range query)
    (restricted : PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) ≠ false)
    (role : PqxdhRecordLiftInterface.Role) : handles role [⟨.inl query, reply⟩] = [] := by
  cases query with
  | inl coin => cases role <;> rfl
  | inr command =>
      cases command <;> cases role <;>
        simp_all [PqxdhDeploymentSecrecy.coinOrSend, RegistrationNativeInterface.eraseCore,
          RegistrationNativeInterface.eraseCommand, handles]

include storage rawStep

/-- The actual coins-and-sends program preserves every installation ordinal and already hidden physical handle. -/
theorem restricted (work : OracleComp RegistrationNativeInterface.Spec Value)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) = false) 0)
    (before : NativeState) (result : Value × NativeState) (prior : valid before)
    (supported : result ∈ support ((simulateQ native work).run before)) :
    Storage slots valid before result.2 ∧ ∀ role, messages role (events result.2) = messages role (events before) := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨⟨prior, fun _ present => present⟩, fun _ => rfl⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have allowed := bounded.1.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, later⟩ := supported
      have first := storage query before middle prior called
      have last := ih middle.1 (by simpa using bounded.2 middle.1) middle.2 result first.1 later
      refine ⟨⟨last.1.1, forward_trans slots before middle.2 result.2 first.2 last.1.2⟩, ?_⟩
      intro role
      exact (last.2 role).trans (RegistrationNativeInstallStep.quiet role _ _ _ _ _
        (rawStep query before middle prior called role) (restricted_handles query middle.1 allowed role))

end BeaconcryptCore.Computational.RegistrationNativeInstallLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallLedger.restricted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallLedger.restricted
