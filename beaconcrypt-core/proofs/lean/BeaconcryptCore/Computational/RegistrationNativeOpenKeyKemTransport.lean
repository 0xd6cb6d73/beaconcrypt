-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic
import BeaconcryptCore.Computational.RegistrationNativeOpenKey

/-! Retained preparation, flag allocation and the actual key108 compiler preserve indexed KEM birth/reveal costs. Their ordinary branches emit no KEM operation; the KEM branches forward the literal original query. Reassociation changes only the oracle sum constructors. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport
open RegistrationNativeKemBeaconFootprint (Kind)
open RegistrationNativeOpenKeyKemPublic (RoutedPrivate)
variable {n : Nat} {KemSK Value : Type} {kind : Kind}

def RetainedPrivate (kind : Kind) : (RegistrationNativeOpenRetained.Spec KemSK).Domain → Prop
  | .inr query => RoutedPrivate (KemSK := KemSK) kind query
  | _ => False
def PhasePrivate (kind : Kind) : (RegistrationNativeOpenKey.PhaseSpec KemSK).Domain → Prop
  | .inr query => RoutedPrivate (KemSK := KemSK) kind query
  | _ => False
def KeyPrivate (kind : Kind) : (RegistrationNativeOpenKey.Spec KemSK).Domain → Prop
  | .inr query => RoutedPrivate (KemSK := KemSK) kind query
  | _ => False

instance (kind : Kind) : DecidablePred (RetainedPrivate (KemSK := KemSK) kind) := fun query => by
  cases query <;> simp only [RetainedPrivate] <;> infer_instance
instance (kind : Kind) : DecidablePred (PhasePrivate (KemSK := KemSK) kind) := fun query => by
  cases query <;> simp only [PhasePrivate] <;> infer_instance
instance (kind : Kind) : DecidablePred (KeyPrivate (KemSK := KemSK) kind) := fun query => by
  cases query <;> simp only [KeyPrivate] <;> infer_instance

private theorem base_zero (work : OracleComp RegistrationNativeRetainedService.Spec Value) :
    (simulateQ (RegistrationNativeOpenRetained.baseLift (KemSK := KemSK)) work).IsQueryBoundP
      (RetainedPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp [RegistrationNativeOpenRetained.baseLift, RetainedPrivate, isQueryBoundP_query_iff]

private theorem ordinary_zero (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    ((RegistrationNativeOpenRetained.ordinary hmac work).run before).IsQueryBoundP
      (RetainedPrivate (KemSK := KemSK) kind) 0 := by
  simp only [RegistrationNativeOpenRetained.ordinary, StateT.run, isQueryBoundP_map_iff]
  exact base_zero _

private theorem compiler_step {ι : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    ((RegistrationNativeOpenRetained.compiler setup wire route sign query).run before).IsQueryBoundP
      (RetainedPrivate (KemSK := KemSK) kind)
      (if RegistrationNativeOpenKeyKemPublic.IsPrivate (KemSK := KemSK) kind query then 1 else 0) := by
  rcases query with (message | (message | query) | query) | query
  · simp [RegistrationNativeOpenRetained.compiler, StateT.run_lift, bind_pure_comp,
      RegistrationNativeOpenRetained.baseLift, RetainedPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · simp [RegistrationNativeOpenRetained.compiler, StateT.run_lift, bind_pure_comp,
      RegistrationNativeOpenRetained.baseLift, RetainedPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · exact ordinary_zero _ _ before
  · simp only [RegistrationNativeOpenRetained.compiler, StateT.run_lift, bind_pure_comp,
      RegistrationNativeOpenRetained.kemLift, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
      RetainedPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate]
    intro counted
    rw [ite_eq_left counted]
    exact Nat.zero_lt_one
  · exact ordinary_zero _ _ before

/-- The actual open retained compiler preserves private KEM costs on arbitrary adaptive frontend work. -/
theorem retained_bound {ι : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeOpenKeyKemPublic.IsPrivate (KemSK := KemSK) kind) count)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (RegistrationNativeOpenRetained.client setup wire route sign work before).IsQueryBoundP
      (RetainedPrivate (KemSK := KemSK) kind) count := by
  simp only [RegistrationNativeOpenRetained.client, StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using compiler_step (kind := kind) setup wire route sign query current
  · intro query free current
    simpa only [ite_eq_right free] using compiler_step (kind := kind) setup wire route sign query current

private theorem phase_base_zero (work : OracleComp RegistrationNativeKeyPhases.Spec Value) :
    (simulateQ (RegistrationNativeOpenKey.phaseLift (KemSK := KemSK)) work).IsQueryBoundP
      (PhasePrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp [RegistrationNativeOpenKey.phaseLift, PhasePrivate, isQueryBoundP_query_iff]

private theorem phase_step (query : (RegistrationNativeOpenRetained.Spec KemSK).Domain)
    (before : RegistrationNativeRetainedService.Flags) :
    ((RegistrationNativeOpenKey.phaseCompiler query).run before).IsQueryBoundP (PhasePrivate (KemSK := KemSK) kind)
      (if RetainedPrivate (KemSK := KemSK) kind query then 1 else 0) := by
  cases query with
  | inl query => exact phase_base_zero _
  | inr query =>
      simp only [RegistrationNativeOpenKey.phaseCompiler, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff, RetainedPrivate, PhasePrivate]
      intro counted
      rw [ite_eq_left counted]
      exact Nat.zero_lt_one

/-- Preparation flags retain the exact opaque indexed-KEM allowance. -/
theorem phase_bound (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RetainedPrivate (KemSK := KemSK) kind) count) :
    (RegistrationNativeOpenKey.phaseClient work).IsQueryBoundP (PhasePrivate (KemSK := KemSK) kind) count := by
  simp only [RegistrationNativeOpenKey.phaseClient, StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using phase_step (KemSK := KemSK) (kind := kind) query current
  · intro query free current
    simpa only [ite_eq_right free] using phase_step (KemSK := KemSK) (kind := kind) query current

private theorem key_base_zero (work : OracleComp RegistrationNativeKeyHybrid.Spec Value) :
    (simulateQ (RegistrationNativeOpenKey.keyLift (KemSK := KemSK)) work).IsQueryBoundP
      (KeyPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp [RegistrationNativeOpenKey.keyLift, KeyPrivate, isQueryBoundP_query_iff]

private theorem key_step (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : (RegistrationNativeOpenKey.PhaseSpec KemSK).Domain) (before : RegistrationNativeKeyPhases.Meta) :
    ((RegistrationNativeOpenKey.keyCompiler source input inside query).run before).IsQueryBoundP
      (KeyPrivate (KemSK := KemSK) kind) (if PhasePrivate (KemSK := KemSK) kind query then 1 else 0) := by
  cases query with
  | inl query => exact key_base_zero _
  | inr query =>
      simp only [RegistrationNativeOpenKey.keyCompiler, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff, PhasePrivate, KeyPrivate]
      intro counted
      rw [ite_eq_left counted]
      exact Nat.zero_lt_one

/-- The native key108 compiler neither adds nor removes private KEM operations. -/
theorem key_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RetainedPrivate (KemSK := KemSK) kind) count) :
    (RegistrationNativeOpenKey.client source input inside work).IsQueryBoundP (KeyPrivate (KemSK := KemSK) kind) count := by
  simp only [RegistrationNativeOpenKey.client, StateT.run'_eq, isQueryBoundP_map_iff]
  apply (phase_bound work count bounded).simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using key_step (KemSK := KemSK) (kind := kind) source input inside query current
  · intro query free current
    simpa only [ite_eq_right free] using key_step (KemSK := KemSK) (kind := kind) source input inside query current

private theorem native_step (query : (RegistrationNativeOpenKey.Spec KemSK).Domain) :
    (RegistrationNativeOpenKey.native query).IsQueryBoundP
      (RegistrationNativeKemCompilerFootprint.predicate RegistrationNativeOpenKey.Ambient KemSK kind)
      (if KeyPrivate (KemSK := KemSK) kind query then 1 else 0) := by
  rcases query with key | ((other | key) | (pool | key))
  all_goals first | cases pool | skip
  all_goals cases kind <;> simp [RegistrationNativeOpenKey.native, KeyPrivate, RoutedPrivate,
    RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]

/-- Reassociation preserves exact native indexed creation/reveal classes, with the uniform108 table in the ambient branch. -/
theorem native_bound (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (KeyPrivate (KemSK := KemSK) kind) count) :
    (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemCompilerFootprint.predicate RegistrationNativeOpenKey.Ambient KemSK kind) count :=
  RawCtxSourceOpen.simulate_bound _ _ _ work count bounded native_step

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.retained_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.phase_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.phase_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.key_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport.native_bound
