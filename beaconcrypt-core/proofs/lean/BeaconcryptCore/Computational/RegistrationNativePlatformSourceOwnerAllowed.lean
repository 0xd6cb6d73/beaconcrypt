-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint
import BeaconcryptCore.Computational.RegistrationPublicationQuerySafety
/-! The actual source bundle lowers every role primitive locally before reaching the trusted interface. The stateful source writer contributes only external coins in the joint language. These structural facts hold for every request reply and every failure branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed
open RegistrationNativePlatformGenericBundle (Spec M liftLegacy trustedLift encoder program)
open RegistrationPublicationQuerySafety (Safe pure_safe bind_safe)
variable {n : Nat} {I E KemSK Auxiliary A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit

def Counted : (Spec E n KemSK).Domain → Prop
  | .inl query => RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .other query
  | .inr _ => False
instance : DecidablePred (Counted (E := E) (n := n) (KemSK := KemSK)) := fun query => by
  cases query with
  | inl query => exact inferInstanceAs (Decidable (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .other query))
  | inr query => exact isFalse (fun h => h)
abbrev Allowed (query : (Spec E n KemSK).Domain) : Prop := ¬ Counted (E := E) (n := n) (KemSK := KemSK) query

theorem lift_safe (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (quiet : RegistrationNativeKemBeaconFootprint.Bounded .other 0 work) :
    Safe (queries := Spec E n KemSK) (Allowed (E := E) (n := n) (KemSK := KemSK)) (liftLegacy (trustedLift (E := E) (KemSK := KemSK)) work) := by
  intro owners env
  apply (isQueryBoundP_zero_iff _ (Allowed (E := E) (n := n) (KemSK := KemSK))).mp
  simp only [Allowed, not_not]
  change (simulateQ (trustedLift (E := E) (n := n) (KemSK := KemSK)) ((work.run owners).run env)).IsQueryBoundP (Counted (E := E) (n := n) (KemSK := KemSK)) 0
  have bounded : ((work.run owners).run env).IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .other) 0 := by
    exact quiet owners env
  apply bounded.simulateQ_of_step
  · intro query paid
    simp [trustedLift, Counted, isQueryBoundP_query_iff]
  · intro query free
    simp only [trustedLift, isQueryBoundP_query_iff]
    intro paid
    exact False.elim (free paid)

theorem encoder_safe (view : registration.InitView) :
    Safe (queries := Spec E n KemSK) (Allowed (E := E) (n := n) (KemSK := KemSK))
      (encoder (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) E view) := by
  intro owners env
  apply (isQueryBoundP_zero_iff _ (Allowed (E := E) (n := n) (KemSK := KemSK))).mp
  simp only [Allowed, not_not]
  unfold encoder RegistrationNativePlatformGenericBundle.encoderWith
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, isQueryBoundP_map_iff]
  apply (isQueryBoundP_false _ 0).simulateQ_of_step
  · intro query impossible
    exact False.elim impossible
  · intro query free
    simp [RegistrationNativePlatformGenericBundle.writerLift, Counted, isQueryBoundP_query_iff]

theorem program_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) :
    Safe (queries := Spec E n KemSK) (Allowed (E := E) (n := n) (KemSK := KemSK))
      (program (Auxiliary := Auxiliary) E setup source index) := by
  unfold program RegistrationNativePlatformGenericBundle.bundle
  apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _ _ (by intro owners env; exact allQueriesSatisfy_pure _ _)
  intro owners
  cases found : owners[index]? with
  | none => exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _
  | some owner =>
      cases phase : owner.phase <;> simp only [phase]
      all_goals try exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _
      all_goals
        apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _ _ (by first
          | exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _
          | exact lift_safe _ (RegistrationNativeKemBeaconFootprint.sample_zero .other _))
        intro oneTime
        apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _ _
          (RegistrationPublicationQuerySafety.Beacon.begin (Allowed (E := E) (n := n) (KemSK := KemSK)) _
            (fun query => lift_safe _ (RegistrationNativeKemBeaconFootprint.outgoing_zero setup .other index owner query))
            _ (encoder_safe) _ _ _ _)
        intro published
        cases published with
        | fail error | div => exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _
        | ok result => cases result with
          | Err previous => exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _
          | Ok finished =>
              simp only
              apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _ _ (lift_safe _ (by
                intro current env
                simp [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify]))
              intro changed
              exact bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _ _
                (lift_safe _ (RegistrationNativeKemBeaconFootprint.effect_zero .other _))
                (fun _ => pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK)) _)

theorem trusted_allowed (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Allowed (E := E) (KemSK := KemSK) (.inl query) ↔ RegistrationNativePublicSourceTrusted.Allowed (KemSK := KemSK) query := by
  rcases query with effect | role | (pool | key)
  · simp [Allowed, Counted, RegistrationNativeKemBeaconFootprint.counted, RegistrationNativePublicSourceTrusted.Allowed]
  · simp [Allowed, Counted, RegistrationNativeKemBeaconFootprint.counted, RegistrationNativePublicSourceTrusted.Allowed]
  · cases pool <;> simp [Allowed, Counted, RegistrationNativeKemBeaconFootprint.counted, RegistrationNativePublicSourceTrusted.Allowed]
  · simp [Allowed, Counted, RegistrationNativeKemBeaconFootprint.counted, RegistrationNativePublicSourceTrusted.Allowed]

private theorem coins_safe (work : ProbComp A) :
    (simulateQ (RegistrationNativePlatformSourceOwnerLanguage.coins (n := n) (KemSK := KemSK)) work).AllQueriesSatisfy
      (RegistrationNativePlatformSourceOwnerJoint.Allowed (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformSourceOwnerLanguage.coins]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨True.intro, ih⟩

/-- The source bundle's actual writer and trusted request lowering preserve the derived role restriction, with arbitrary P updates. -/
theorem compiled_safe {Platform : Type}
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (Spec E n KemSK) A) (allowed : work.AllQueriesSatisfy (Allowed (E := E) (KemSK := KemSK))) (previous : Platform) :
    ((simulateQ (RegistrationNativePlatformSourceOwnerLanguage.handler writer) work).run previous).AllQueriesSatisfy
      (RegistrationNativePlatformSourceOwnerJoint.Allowed (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply allQueriesSatisfy_bind
    · cases query with
      | inl query =>
        simp only [RegistrationNativePlatformSourceOwnerLanguage.handler, RegistrationNativePlatformSourceOwnerLanguage.trusted,
          StateT.run_lift, bind_pure_comp, map_eq_bind_pure_comp, allQueriesSatisfy_query_bind_iff]
        exact ⟨(trusted_allowed (E := E) (KemSK := KemSK) query).mp allowed.1, fun _ => allQueriesSatisfy_pure _ _⟩
      | inr query => exact coins_safe ((writer query).run previous)
    · intro result
      exact ih result.1 (allowed.2 result.1) result.2

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.lift_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.lift_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.encoder_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.encoder_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.program_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.trusted_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.trusted_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.compiled_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed.compiled_safe
