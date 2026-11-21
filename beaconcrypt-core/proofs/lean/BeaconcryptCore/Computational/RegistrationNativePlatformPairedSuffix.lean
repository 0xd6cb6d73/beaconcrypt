-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects
import BeaconcryptCore.Computational.RegistrationNativePairedSafe
/-! The literal native paired observer validates a suffix with one possible installation against the actual immediately preceding material reply. No preparation/demand can intervene inside that suffix. These structural hypotheses are discharged from the actual new source bodies in the enclosing compiler theorem; they are not a security or whole-callback contract. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedSuffix
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePairedTrace (State step handler Fits FitsKernel)
open RegistrationNativePairedSafe (GlobalInstall)
variable {n : Nat} {KemSK Value : Type}

def Allowed (role : Role) (choice : Choice n) : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inr (.inr query)))) => RegistrationNativePairedProvenance.Effect role choice query
  | _ => True

def Active (choice : Choice n) (message : Message) (before : State n) : Prop :=
  before.trace.current = some message ∧ before.choice = some choice

def RootFree : (Spec n KemSK).Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr (.inl (.inl _))) => False
  | _ => True
instance : DecidablePred (RootFree (n := n) (KemSK := KemSK)) := fun query => by
  unfold RootFree
  split <;> infer_instance

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
  · simpa only [Ready, Active, step, Fits, RegistrationNativePairedTrace.updateChoice,
      RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
      GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
      ite_false, Nat.sub_zero, decide_true, Bool.not_true, Bool.or_false] using ready
  · rcases environment with coin | capability
    · simpa only [Ready, Active, step, Fits, RegistrationNativePairedTrace.updateChoice,
        RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
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
      | _ => simpa only [Ready, Active, step, Fits, RegistrationNativePairedTrace.updateChoice,
          RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
          GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
          RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, ite_false, Nat.sub_zero,
          decide_true, Bool.not_true, Bool.or_false] using ready
  all_goals simpa only [Ready, Active, step, Fits, RegistrationNativePairedTrace.updateChoice,
    RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
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

end BeaconcryptCore.Computational.RegistrationNativePlatformPairedSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedSuffix.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedSuffix.suffix
