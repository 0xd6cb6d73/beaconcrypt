-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix

/-! Native programs with zero actual installation bills preserve a clean paired monitor. The predicate names the literal callbacks rather than successful World updates, so failed attempts and stale prior descriptor/choice state remain covered. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedSafe
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePairedTrace (State Safe Fits step handler)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
variable {n : Nat} {KemSK Value : Type}

def GlobalInstall (role : Role) : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inr query))) => Install role query
  | _ => False
instance (role : Role) : DecidablePred (GlobalInstall (n := n) (KemSK := KemSK) role) := fun query => by
  rcases query with (prepare | (demand | common) | kem) | record
  · exact isFalse id
  · exact isFalse id
  · exact inferInstanceAs (Decidable (Install role common))
  · exact isFalse id
  · exact isFalse id

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

/-- Every actual native callback program with zero installation allowances preserves the complete clean paired observer. -/
theorem free (work : OracleComp (Spec n KemSK) Value)
    (bounded : ∀ role, work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0) : Safe work := by
  intro before result clean supported
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact RegistrationNativePairedTrace.pure_safe value before result clean supported
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
/-- Native routing forwards each literal Common installation once and all KEM capabilities remain installation-free. -/
theorem local_bound (role : Role) (selected : Bool)
    (work : OracleComp (RegistrationNativePublicFrontend.LocalSpec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall (KemSK := KemSK) role) cap) :
    (simulateQ (RegistrationNativePublicFrontend.liftLocal selected) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  rcases query with message | (message | common) | kem
  · simp [RegistrationNativePublicFrontend.liftLocal, GlobalInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]
  · simp [RegistrationNativePublicFrontend.liftLocal, GlobalInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]
  · simp [RegistrationNativePublicFrontend.liftLocal, GlobalInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]
    intro counted
    rw [ite_eq_left counted]
    decide
  · rcases kem with other | (pool | key)
    · simp [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route, RegistrationNativePublicFrontend.liftRoutedKem,
        GlobalInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]
    · simp [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route, RegistrationNativePublicFrontend.liftRoutedKem,
        GlobalInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]
    · cases selected <;> simp [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route, RegistrationNativePublicFrontend.liftRoutedKem,
        GlobalInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]
end BeaconcryptCore.Computational.RegistrationNativePairedSafe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedSafe.free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedSafe.free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedSafe.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedSafe.local_bound
