-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedTrace

/-! The paired monitor is clean for installation-free native prefixes and for every root-free material suffix whose original structural role bill is at most one. The suffix proof checks the returned slot against its actual current demand before the insertion, then uses the remaining zero bill through all subsequent continuations. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordPairedTrace (State step handler Fits FitsKernel Safe)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallTrace (RootFree)
variable {n : Nat} {KemSK Value : Type}

def Allowed (role : Role) (choice : Choice n) : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inr (.inr query)))) => RegistrationNativePairedProvenance.Effect role choice query
  | _ => True

def Active (choice : Choice n) (message : Message) (before : State n) : Prop :=
  before.trace.current = some message ∧ before.choice = some choice

private theorem allowed_quiet (role : Role) (choice : Choice n) (request : (Spec n KemSK).Domain)
    (quiet : ∀ actual, ¬ GlobalInstall actual request) : Allowed role choice request := by
  rcases request with (prepare | (demand | (publication | environment)) | kem) | record
  · trivial
  · trivial
  · trivial
  · rcases environment with coin | capability
    · trivial
    · cases capability with
      | installServer keyId binding kernel => exact False.elim (quiet .server rfl)
      | installBeacon owner shell kernel => exact False.elim (quiet .beacon rfl)
      | _ => trivial
  · trivial
  · trivial

/-- Compilation prefixes with zero role bills cannot contain an unrelated hidden-slot installation. -/
theorem free_allowed (role : Role) (choice : Choice n) (work : OracleComp (Spec n KemSK) Value)
    (bounded : ∀ actual, work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) actual) 0) :
    AllQueriesSatisfy work (Allowed (KemSK := KemSK) role choice) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind request next ih =>
      have head := fun actual => (isQueryBoundP_query_bind_iff _ _ _ _).mp (bounded actual)
      refine ⟨allowed_quiet role choice request (fun actual => (head actual).1.resolve_right (by omega)), ?_⟩
      intro reply
      exact ih reply (fun actual => by simpa only [Nat.zero_sub, ite_self] using (head actual).2 reply)

private theorem fits_free (request : (Spec n KemSK).Domain) (before : State n)
    (quiet : ∀ role, ¬ GlobalInstall role request) : Fits request before := by
  rcases request with (prepare | (demand | (publication | environment)) | kem) | record
  · trivial
  · trivial
  · trivial
  · rcases environment with coin | capability
    · trivial
    · cases capability with
      | installServer keyId binding kernel => exact False.elim (quiet .server rfl)
      | installBeacon owner shell kernel => exact False.elim (quiet .beacon rfl)
      | _ => trivial
  · trivial
  · trivial

/-- Every actual program with zero installation bills preserves a clean paired monitor, even when it prepares or demands roots. -/
theorem free (work : OracleComp (Spec n KemSK) Value)
    (bounded : ∀ role, work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0) : Safe work := by
  intro before result clean supported
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact RegistrationNativeSecretWordPairedTrace.pure_safe value before result clean supported
  | query_bind request next ih =>
      have head := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (bounded role)
      have quiet : ∀ role, ¬ GlobalInstall role request := fun role => (head role).1.resolve_right (by omega)
      have valid := fits_free request before quiet
      have cleanStep (reply : (Spec n KemSK).Range request) : (step request reply before).bad = false := by
        simp only [step, valid, decide_true, Bool.not_true, Bool.or_false, clean]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      exact ih reply (fun role => by simpa only [Nat.zero_sub, ite_self] using (head role).2 reply)
        _ (cleanStep reply) continued

private theorem fits_active (before : State n) (choice : Choice n) (message : Message)
    (active : Active choice message before) (kernel : PqxdhRecordLiftInterface.KernelRef n)
    (allowed : RegistrationNativePairedProvenance.Kernel choice kernel) : FitsKernel before kernel := by
  cases kernel with
  | known kernel => trivial
  | hidden slot =>
      obtain ⟨reference, same, assigned⟩ := allowed
      exact ⟨by simp only [active.1, Option.isSome_some], reference, active.2.trans (congrArg some same), assigned⟩

def Ready (choice : Choice n) (message : Message) (cap : Nat) (before : State n) : Prop :=
  before.bad = false ∧ (cap = 0 ∨ Active choice message before)

private theorem query (role : Role) (choice : Choice n) (message : Message)
    (request : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range request)
    (cap : Nat) (small : cap ≤ 1) (before : State n)
    (quiet : RootFree request) (allowed : Allowed role choice request)
    (room : ¬ GlobalInstall role request ∨ 0 < cap) (ready : Ready choice message cap before) :
    Ready choice message (cap - if GlobalInstall role request then 1 else 0) (step request reply before) := by
  rcases request with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · exact False.elim quiet
  · exact False.elim quiet
  · simpa only [Ready, Active, step, Fits, RegistrationNativeSecretWordPairedTrace.updateChoice,
      RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
      GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
      ite_false, Nat.sub_zero, decide_true, Bool.not_true, Bool.or_false] using ready
  · rcases environment with coin | capability
    · simpa only [Ready, Active, step, Fits, RegistrationNativeSecretWordPairedTrace.updateChoice,
        RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
        GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
        RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, ite_false, Nat.sub_zero,
        decide_true, Bool.not_true, Bool.or_false] using ready
    · cases capability with
      | installServer keyId binding kernel =>
          obtain ⟨rfl, compatible⟩ := allowed
          have positive : 0 < cap := room.resolve_left (by simp [GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
            RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])
          have active := ready.2.resolve_left (by omega)
          have fits : Fits (n := n) (KemSK := KemSK)
              (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding kernel))))))) before :=
            fits_active before choice message active kernel compatible
          refine ⟨?_, Or.inl (by simp only [GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
            RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, ite_true]; omega)⟩
          simp only [step, fits, decide_true, Bool.not_true, Bool.or_false, ready.1]
      | installBeacon owner shell kernel =>
          obtain ⟨rfl, compatible⟩ := allowed
          have positive : 0 < cap := room.resolve_left (by simp [GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
            RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])
          have active := ready.2.resolve_left (by omega)
          have fits : Fits (n := n) (KemSK := KemSK)
              (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell kernel))))))) before :=
            fits_active before choice message active kernel compatible
          refine ⟨?_, Or.inl (by simp only [GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
            RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, ite_true]; omega)⟩
          simp only [step, fits, decide_true, Bool.not_true, Bool.or_false, ready.1]
      | _ => simpa only [Ready, Active, step, Fits, RegistrationNativeSecretWordPairedTrace.updateChoice,
          RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
          GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
          RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, ite_false, Nat.sub_zero,
          decide_true, Bool.not_true, Bool.or_false] using ready
  all_goals simpa only [Ready, Active, step, Fits, RegistrationNativeSecretWordPairedTrace.updateChoice,
    RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
    GlobalInstall, ite_false, Nat.sub_zero, decide_true, Bool.not_true, Bool.or_false] using ready

/-- The exact root-free suffix checks its one possible installation against the current descriptor and the actual returned hidden reference. -/
theorem suffix (role : Role) (choice : Choice n) (message : Message) (work : OracleComp (Spec n KemSK) Value)
    (cap : Nat) (small : cap ≤ 1) (bounded : work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap)
    (quiet : work.IsQueryBoundP (fun query => ¬ RootFree (KemSK := KemSK) query) 0)
    (allowed : AllQueriesSatisfy work (Allowed (KemSK := KemSK) role choice)) (before : State n)
    (ready : Ready choice message cap before) (result : Value × State n)
    (supported : result ∈ support ((simulateQ handler work).run before)) : result.2.bad = false := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ready.1
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded quiet
      obtain ⟨headAllowed, restAllowed⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      have rootfree : RootFree request := not_not.mp (quiet.1.resolve_right (by omega))
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      have stepped := query role choice message request reply cap small before rootfree headAllowed bounded.1 ready
      have cost : cap - (if GlobalInstall role request then 1 else 0) =
          (if GlobalInstall role request then cap - 1 else cap) := by split <;> simp_all
      rw [cost] at stepped
      exact ih reply _ (by split <;> omega) (bounded.2 reply)
        (by simpa only [Nat.zero_sub, ite_self] using quiet.2 reply) (restAllowed reply) _ stepped continued

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe.free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe.free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe.free_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe.free_allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe.suffix
