-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
/-! The literal shared-state Init writer and outgoing controller never create a private KEM row. Every signing failure, mutable writer result and source owner update is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleBirth
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Trusted Owner)
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Auxiliary E A B Value Next : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
namespace Native
def Allowed : (Trusted n KemSK).Domain → Prop :=
  fun query => ¬RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create query
def Safe (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env, AllQueriesSatisfy ((work.run owners).run env) (Allowed (n := n) (KemSK := KemSK))

open RegistrationNativeBeaconFrontend (M State effect sample updateEnv outgoing)
private theorem pure_safe (value : Value) : Safe (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial

private theorem bind_safe (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun reply => later reply.1.1 reply.1.2 reply.2)

private theorem effect_safe (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Safe (effect query : M n KemSK source Auxiliary _) := by
  intro owners env
  simp only [effect, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr (by simp only [Allowed, RegistrationNativeKemBeaconFootprint.counted, not_false_eq_true]))

private theorem sample_safe (work : ProbComp Value) : Safe (sample work : M n KemSK source Auxiliary Value) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe value
  | query_bind query next ih =>
      simp only [sample, simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (effect_safe _) ih

private theorem modify_safe (change : State source → State source) :
    Safe (modify change : M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure]
  trivial

private theorem update_safe (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (updateEnv change : M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [updateEnv, StateT.run_lift]
  trivial

private theorem program_safe {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (step : ∀ query, Safe (implementation query)) (work : OracleComp spec Value) : Safe (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (step query) ih

private theorem outgoing_safe (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Safe (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect_safe _
    | sign _ _ _ => exact pure_safe _
  | inr request =>
      simp only [outgoing]
      split
      · exact bind_safe _ _ (modify_safe _) (fun _ => pure_safe _)
      · exact pure_safe _


end Native
open RegistrationNativePlatformGenericBundle (M Spec liftLegacy trustedLift)
def Allowed : (Spec E n KemSK).Domain → Prop
  | .inl query => Native.Allowed (KemSK := KemSK) query
  | .inr _ => True
def Safe (work : M source Auxiliary (OracleComp (Spec E n KemSK)) A) : Prop :=
  ∀ owners env, AllQueriesSatisfy ((work.run owners).run env) (Allowed (E := E) (KemSK := KemSK))
private theorem pure_free (value : A) : Safe (pure value : M source Auxiliary (OracleComp (Spec E n KemSK)) A) :=
  fun _ _ => allQueriesSatisfy_pure _ _
private theorem bind_free (work : M source Auxiliary (OracleComp (Spec E n KemSK)) A)
    (next : A → M source Auxiliary (OracleComp (Spec E n KemSK)) B)
    (prior : Safe work) (later : ∀ value, Safe (next value)) : Safe (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (prior owners env) (fun result => later result.1.1 result.1.2 result.2)
private theorem legacy_free (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (free : Native.Safe work) : Safe (E := E) (liftLegacy trustedLift work) := by
  intro owners env
  unfold liftLegacy
  apply simulation _ _ _ _ _ (free owners env)
  intro query safe
  exact (allQueriesSatisfy_query_iff _ _).mpr safe
private theorem get_free : Safe (get : M source Auxiliary (OracleComp (Spec E n KemSK)) (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env
  simp only [StateT.run_get, StateT.run_pure]
  trivial

private abbrev Carrier (A : Type) :=
  {work : M source Auxiliary (OracleComp (Spec E n KemSK)) A // Safe work}
private abbrev carrierMonad : Monad (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)) where
  pure value := ⟨pure value, pure_free value⟩
  bind work next := ⟨work.val >>= fun value => (next value).val, bind_free _ _ work.property (fun value => (next value).property)⟩

private theorem publication_free (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (encode : registration.InitView → M source Auxiliary (OracleComp (Spec E n KemSK)) (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : ∀ packet, Safe (encode packet)) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Safe (RegistrationNativePlatformBeaconPublication.begin
      (fun query => liftLegacy trustedLift (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
      encode ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin) := by
  let _ := carrierMonad (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
  let _ : LawfulMonad (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)) := LawfulMonad.mk' _
    (fun work => by apply Subtype.ext; exact bind_pure work.val)
    (fun value next => by apply Subtype.ext; exact pure_bind value (fun value => (next value).val))
    (fun work next rest => by apply Subtype.ext; exact bind_assoc work.val (fun value => (next value).val) (fun value => (rest value).val))
  let forget : ∀ {A : Type}, Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) A → M source Auxiliary (OracleComp (Spec E n KemSK)) A := fun {_} work => work.val
  have hom : Cslib.IsMonadHom (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)) (M source Auxiliary (OracleComp (Spec E n KemSK))) forget := .mk' (fun _ => rfl) (fun _ _ => rfl)
  let operations : QueryImpl RegistrationBeaconInitExecutor.Spec (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)) :=
    fun query => ⟨liftLegacy trustedLift (RegistrationNativeBeaconFrontend.outgoing setup source index owner query), legacy_free _ (Native.outgoing_safe setup index owner query)⟩
  let encoding : registration.InitView → Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (RustM (core.option.Option (alloc.vec.Vec U8))) := fun packet => ⟨encode packet, writer packet⟩
  have kept := (RegistrationNativePlatformBeaconPublication.begin operations encoding ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin).property
  change Safe (forget (RegistrationNativePlatformBeaconPublication.begin operations encoding _ _ _ _)) at kept
  rw [RegistrationNativePlatformBeaconMap.begin hom] at kept
  exact kept

theorem bundle_free (setup : Setup base KemSK)
    (encode : registration.InitView → M source Auxiliary (OracleComp (Spec E n KemSK)) (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : ∀ packet, Safe (encode packet)) (index : Nat) :
    Safe (RegistrationNativePlatformGenericBundle.bundle trustedLift setup source encode index) := by
  unfold RegistrationNativePlatformGenericBundle.bundle
  apply bind_free _ _ (get_free)
  intro owners
  cases found : owners[index]? with
  | none => exact pure_free _
  | some owner =>
    have finish (oneTime : PqxdhJointGapDh.ScalarBytes) := publication_free setup index owner encode writer oneTime
    cases phase : owner.phase with
    | fresh | freshWithCoins scalar =>
      simp only [phase]
      apply bind_free _ _
      · first
        | exact legacy_free _ (Native.sample_safe _)
        | exact pure_free _
      · intro oneTime
        apply bind_free _ _ (finish oneTime)
        intro published
        cases published with
        | fail error | div => exact pure_free _
        | ok result => cases result with
          | Err previous => exact pure_free _
          | Ok finished =>
            apply bind_free _ _ (legacy_free _ (Native.modify_safe _))
            intro _
            apply bind_free _ _ (legacy_free _ (Native.effect_safe _))
            intro _
            exact pure_free _
    | initSent pending scalar | established completed | aborted previous =>
      simp only [phase]
      exact pure_free _

private theorem every_query {I A : Type} {spec : OracleSpec I} (work : OracleComp spec A) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem encoder_free (view : registration.InitView) :
    Safe (RegistrationNativePlatformGenericBundle.encoder (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) E view) := by
  intro owners env
  simp only [RegistrationNativePlatformGenericBundle.encoder, RegistrationNativePlatformGenericBundle.encoderWith,
    StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  apply mapped
  apply simulation _ (fun _ => True) _ _ _ (every_query _)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

/-- The literal dynamic writer bundle performs no private KEM birth. -/
theorem program_free (setup : Setup base KemSK) (index : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    AllQueriesSatisfy (((RegistrationNativePlatformGenericBundle.program (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) E setup source index).run owners).run env)
      (Allowed (E := E) (KemSK := KemSK)) :=
  bundle_free setup _ (encoder_free) index owners env
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleBirth.bundle_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleBirth.bundle_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleBirth.program_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleBirth.program_free
