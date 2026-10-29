-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace

/-! A root-free material suffix can retain or clear the actual current demand, but cannot change its descriptor. Each actual role installation contributes at most its current atom bit to the trace. This operational statement preserves the complete callback AST and does not reset a stale trace entry. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordFrontendTrace (Event State handler begin finish)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
variable {n : Nat} {KemSK Value : Type}

def atom : Option Message → Nat
  | none => 0
  | some message => match message.kem with | .atom => 1 | .literal _ => 0

def attempt (role : Role) : Event → Bool
  | .installAttempt actual message => decide (role = actual) && decide (atom (some message) = 1)
  | _ => false

def count (role : Role) (before : State) : Nat := before.events.countP (attempt role)

def RootFree : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr (.inl (.inl _))) => False
  | _ => True
instance : DecidablePred (RootFree (n := n) (KemSK := KemSK)) := fun query => by
  unfold RootFree
  split <;> infer_instance

private theorem atom_le (message : Option Message) : atom message ≤ 1 := by
  cases message with
  | none => simp only [atom]; decide
  | some message => cases formed : message.kem <;> simp only [atom, formed] <;> decide

private theorem attempt_step (role actual : Role) (before : State) :
    count role (RegistrationNativeSecretWordFrontendTrace.attempt actual before) =
      count role before + if role = actual then atom before.current else 0 := by
  cases formed : before.current with
  | none => simp only [RegistrationNativeSecretWordFrontendTrace.attempt, formed, count, atom]; split <;> omega
  | some message =>
      cases word : message.kem <;> cases role <;> cases actual <;>
        simp [RegistrationNativeSecretWordFrontendTrace.attempt, formed, count, List.countP_append, attempt, atom, word]

private theorem installed_step (role actual : Role) (reply : Bool) (before : State) :
    count role (RegistrationNativeSecretWordFrontendTrace.installed actual reply before) = count role before := by
  cases reply <;> cases formed : before.current <;>
    simp [RegistrationNativeSecretWordFrontendTrace.installed, count, formed, List.countP_append, attempt]

/-- Every actual root-free callback keeps or clears the current atom, and records at most its own role installation attempt. -/
theorem query (role : Role) (request : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range request) (before : State)
    (quiet : RootFree request) :
    atom (finish request reply (begin request before)).current ≤ atom before.current ∧
      count role (finish request reply (begin request before)) ≤
        count role before + if GlobalInstall role request then atom before.current else 0 := by
  rcases request with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · exact False.elim quiet
  · exact False.elim quiet
  · simp only [begin, finish, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, ite_false]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rcases environment with coin | capability
    · simp only [begin, finish, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
        RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, ite_false]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · cases capability <;>
        simp only [begin, finish, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
          RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, ite_false]
      all_goals first
        | exact ⟨Nat.le_refl _, Nat.le_refl _⟩
        | constructor
          · exact Nat.zero_le _
          · rw [installed_step, attempt_step]
  · simp only [begin, finish, GlobalInstall, ite_false]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · simp only [begin, finish, GlobalInstall, ite_false, count, List.countP_append, List.countP_singleton, attempt,
      Bool.false_eq_true, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · simp only [begin, finish, GlobalInstall, ite_false]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · simp only [begin, finish, GlobalInstall, ite_false, count, List.countP_append, List.countP_singleton, attempt,
      Bool.false_eq_true, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · simp only [begin, finish, GlobalInstall, ite_false]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Root preparation and demand may change the current descriptor, but never add an installation-attempt event themselves. -/
theorem query_upper (role : Role) (request : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range request) (before : State) :
    count role (finish request reply (begin request before)) ≤ count role before +
      if GlobalInstall role request then atom before.current else 0 := by
  rcases request with (message | (message | common) | kem) | record
  · simp [begin, finish, count, List.countP_append, attempt, GlobalInstall]
  · simp [begin, finish, count, List.countP_append, attempt, GlobalInstall]
  · exact (query role _ reply before trivial).2
  · exact (query role _ reply before trivial).2
  · exact (query role _ reply before trivial).2

/-- Any actual callback program with no installation of this role cannot add an attempt of that role, even if it prepares or demands other roots. -/
theorem free (role : Role) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0)
    (before : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ handler work).run before)) : count role result.2 ≤ count role before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact Nat.le_refl _
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have quiet : ¬ GlobalInstall role request := bounded.1.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      have stepped := query_upper role request reply before
      simp only [ite_eq_right quiet, Nat.add_zero] at stepped
      exact (ih reply (by simpa only [ite_self, Nat.zero_sub] using bounded.2 reply) _ continued).trans stepped

/-- A complete root-free callback suffix retains the current descriptor's atom bit and respects its actual structural role-installation cap. -/
theorem program (role : Role) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap)
    (quiet : work.IsQueryBoundP (fun query => ¬ RootFree (KemSK := KemSK) query) 0)
    (before : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ handler work).run before)) :
    atom result.2.current ≤ atom before.current ∧ count role result.2 ≤ count role before + cap * atom before.current := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded quiet
      have rootfree : RootFree request := not_not.mp (quiet.1.resolve_right (by omega))
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      have stepped := query role request reply before rootfree
      have later := ih reply _ (bounded.2 reply) (by simpa only [Nat.zero_sub, ite_self] using quiet.2 reply) _ continued
      refine ⟨later.1.trans stepped.1, ?_⟩
      have mul := Nat.mul_le_mul_left (cap - 1) stepped.1
      by_cases counted : GlobalInstall role request
      · have positive : 0 < cap := bounded.1.resolve_left (not_not.mpr counted)
        simp only [ite_eq_left counted] at stepped later
        have product : (cap - 1) * atom before.current + atom before.current = cap * atom before.current := by
          rw [← Nat.succ_mul]
          congr 1
          omega
        omega
      · simp only [ite_eq_right counted, Nat.add_zero] at stepped
        have mul' := Nat.mul_le_mul_left cap stepped.1
        simp only [ite_eq_right counted] at later
        omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.query_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.query_upper
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace.free
