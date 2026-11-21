-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals
import BeaconcryptCore.Computational.RegistrationNativeInstallPredicate

/-! Installation-free actual callback programs preserve the complete per-role successful descriptor list. The claim retains preparations, demands, attempts and unrelated installations in the original trace. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallTrace
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeG2Trace (State handler begin finish)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
variable {n : Nat} {KemSK Value : Type}

/-- An actual callback outside this role's installation capability preserves all successful descriptors of this role. -/
theorem query_free (role : Role) (request : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (reply : (RegistrationNativePublicFrontend.Spec n KemSK).Range request) (before : State)
    (quiet : ¬ GlobalInstall role request) :
    messages role (finish request reply (begin request before)).events = messages role before.events := by
  rcases request with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · simp [begin, finish, messages, List.filterMap_append]
  · simp [begin, finish, messages, List.filterMap_append]
  · rfl
  · rcases environment with coin | capability
    · rfl
    · cases capability <;> first
      | rfl
      | cases role <;> simp only [GlobalInstall, Install, InstallEnv] at quiet
        all_goals first
          | exact False.elim (quiet trivial)
          | cases reply <;> cases current : before.current <;>
              simp [begin, finish, RegistrationNativeG2Trace.attempt,
                RegistrationNativeG2Trace.installed, current, messages, List.filterMap_append]
  · rfl
  · simp [begin, finish, messages, List.filterMap_append]
  · rfl
  · simp [begin, finish, messages, List.filterMap_append]
  · rfl

/-- Every exact callback program with zero installation bill for this role preserves its successful message list. -/
theorem free (role : Role) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0)
    (before : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ handler work).run before)) :
    messages role result.2.events = messages role before.events := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have quiet : ¬ GlobalInstall role request := bounded.1.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      exact (ih reply (by simpa only [ite_self, Nat.zero_sub] using bounded.2 reply) _ continued).trans
        (query_free role request reply before quiet)
end BeaconcryptCore.Computational.RegistrationNativeInstallTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTrace.query_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTrace.query_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallTrace.free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallTrace.free
