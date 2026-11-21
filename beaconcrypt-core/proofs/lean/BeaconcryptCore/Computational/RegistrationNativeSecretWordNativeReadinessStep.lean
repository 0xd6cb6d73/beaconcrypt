-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness

/-! Every concrete callback preserves reflected native preparation. A checked material demand carries the actual earlier Word preparation certificate, and coherent optional input validity turns that into a native live flag even for byte-aliased descriptors. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessStep
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message eval input)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked Prepared)
open RegistrationNativeSecretWordNativeReadiness (Audit Good valid step)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)

def IsPrepare : (Spec n KemSK).Domain → Prop
  | .inl (.inl _) => True
  | _ => False

/-- Every actual nonpreparation callback retains the complete private descriptor flag function. -/
theorem flags_unchanged (query : (Spec n KemSK).Domain) (quiet : ¬IsPrepare (KemSK := KemSK) query)
    (before : State n KemSK) (result : (Spec n KemSK).Range query × State n KemSK)
    (supported : result ∈ support
      ((handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider query).run before)) :
    result.2.flags = before.flags := by
  rcases query with (message | (message | common) | kem) | record
  · exact (quiet trivial).elim
  · cases formed : input setup.joint setup.dh seed scalar message <;>
      simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.roots,
        RegistrationNativeSecretWordServiceChecked.checked, StateT.run, formed,
        map_pure, Functor.map_map, mem_support_pure_iff, support_map] at supported
    · cases supported
      rfl
    · obtain ⟨output, _called, returned⟩ := supported
      cases returned
      rfl
  all_goals simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.handler,
    RegistrationNativeSecretWordInterpreter.ordinary, RegistrationNativeSecretWordInterpreter.routed,
    StateT.run, support_map] at supported
  all_goals obtain ⟨output, _called, returned⟩ := supported
  all_goals cases returned
  all_goals rfl
/-- Each actual prepared callback preserves reflected native flags and keeps the native unprepared-demand audit false. -/
theorem query_good (query : (Spec n KemSK).Domain) (before : Audit × State n KemSK)
    (good : Good setup seed scalar candidate before.1 before.2)
    (prepared : Prepared (input setup.joint setup.dh seed scalar) query before.2)
    (result : (Spec n KemSK).Range query × (Audit × State n KemSK))
    (supported : result ∈ support
      ((RegistrationNativeSecretWordNativeReadiness.handler setup wire route sign inside provider seed scalar candidate query).run before)) :
    Good setup seed scalar candidate result.2.1 result.2.2 := by
  simp only [RegistrationNativeSecretWordNativeReadiness.handler, StateT.run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  have prior := good
  rcases good with ⟨nativeValid, reflected, clear⟩
  rcases query with (message | (message | common) | kem) | record
  · simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.roots,
      RegistrationNativeSecretWordServiceChecked.checked, RegistrationNativeSecretWordService.handler,
      StateT.run, map_pure, mem_support_pure_iff] at called
    cases called
    refine ⟨RegistrationNativeSecretWordNativeFlags.valid_prepare _ _ nativeValid _, ?_, clear⟩
    exact RegistrationNativeSecretWordNativeFlags.refines_prepare (eval candidate) (valid setup seed scalar)
      before.2.flags before.1.native nativeValid reflected message
      (input setup.joint setup.dh seed scalar message).isSome
      (RegistrationNativeSecretWordNativeFlags.input_coherent setup.joint setup.dh seed scalar candidate message).symm
  · have unchanged := flags_unchanged setup wire route sign inside provider seed scalar
      (.inl (.inr (.inl (.inl message)))) (by exact id) before.2 reached called
    change RegistrationNativeSecretWordNativeFlags.Valid (valid setup seed scalar) before.1.native ∧
      RegistrationNativeSecretWordNativeFlags.Refines (eval candidate) reached.2.flags before.1.native ∧
      (before.1.bad || (valid setup seed scalar (eval candidate message) && !(before.1.native (eval candidate message)))) = false
    rw [unchanged]
    refine ⟨nativeValid, reflected, ?_⟩
    have live : valid setup seed scalar (eval candidate message) = true → before.1.native (eval candidate message) = true := by
      intro active
      have wordValid : (input setup.joint setup.dh seed scalar message).isSome = true :=
        (RegistrationNativeSecretWordNativeFlags.input_coherent setup.joint setup.dh seed scalar candidate message).symm.trans active
      exact reflected message (prepared wordValid)
    by_cases active : valid setup seed scalar (eval candidate message) = true
    · simp only [clear, active, live active, Bool.not_true, Bool.and_false, Bool.or_false]
    · have inactive := Bool.eq_false_iff.mpr active
      simp only [clear, inactive, Bool.false_and, Bool.or_false]
  all_goals have unchanged := flags_unchanged setup wire route sign inside provider seed scalar _ (by exact id) before.2 reached called
  all_goals simpa only [Good, step, unchanged] using prior

end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessStep.flags_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessStep.flags_unchanged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessStep.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessStep.query_good
