-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape
/-! Individual literal SDK agreement and record callbacks preserve their actual primitive/random effects. Only the explicit record commitment request enters the physical shared Env hash backend; indexed KEM, local identity DH, root KDF and bookkeeping do not. The temporary old primitive adapter is checked structurally at these individual source bodies, with no whole-controller equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishPrimitiveHashBounds
open RegistrationNativePlatformIdentityFrontendHashBounds
open RegistrationNativeIdentityFrontend (M Owner)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private def OldIsHash : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain → Prop
  | .inl (.inr (.hash _)) => True
  | _ => False
private instance : DecidablePred (OldIsHash (n := n) (KemSK := KemSK)) := fun query => by
  unfold OldIsHash
  split <;> infer_instance
private def OldBounded (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) (cap : Nat) : Prop :=
  ∀ owners env, ((work.run owners).run env).IsQueryBoundP (OldIsHash (KemSK := KemSK)) cap
private theorem old_pure (value : A) (cap : Nat) : OldBounded (pure value : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) cap :=
  fun _ _ => isQueryBoundP_pure _ _ _
private theorem old_bind (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (next : A → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary B) (first later : Nat)
    (bounded : OldBounded work first) (rest : ∀ value, OldBounded (next value) later) : OldBounded (work >>= next) (first + later) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded owners env) (fun result _ => rest result.1.1 result.1.2 result.2)
private theorem old_effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    OldBounded (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (mldsaSource := source) query)
      (if OldIsHash (KemSK := KemSK) (.inl query) then 1 else 0) := by
  intro owners env
  simp only [RegistrationNativeBeaconFrontend.effect, StateT.run_lift, StateT.run_map, bind_pure_comp,
    Functor.map_map, isQueryBoundP_map_iff]
  by_cases active : OldIsHash (KemSK := KemSK) (.inl query) <;>
    simp only [isQueryBoundP_query_iff, active, ite_true, ite_false] <;> simp
private theorem old_kem (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    OldBounded (RegistrationNativeBeaconFrontend.kem (n := n) (Auxiliary := Auxiliary) (mldsaSource := source) query) 0 := by
  intro owners env
  simp [RegistrationNativeBeaconFrontend.kem, StateT.run_lift, StateT.run_map, bind_pure_comp,
    Functor.map_map, OldIsHash]
private theorem old_sample (work : ProbComp A) :
    OldBounded (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mldsaSource := source) work) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [RegistrationNativeBeaconFrontend.sample, simulateQ_pure] using old_pure (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) value 0
  | query_bind query next ih =>
      simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_bind, simulateQ_spec_query]
      exact old_bind _ _ 0 0 (old_effect (.inl query)) ih
private theorem old_update (update : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    OldBounded (RegistrationNativeBeaconFrontend.updateEnv (n := n) (KemSK := KemSK) (mldsaSource := source) update) 0 := by
  intro owners env
  simp [RegistrationNativeBeaconFrontend.updateEnv, StateT.run_lift]
private theorem old_program_zero {J : Type} {queries : OracleSpec J}
    (callback : QueryImpl queries (RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary))
    (leaf : ∀ query, OldBounded (callback query) 0) (work : OracleComp queries A) : OldBounded (simulateQ callback work) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => exact old_pure value 0
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact old_bind _ _ 0 0 (leaf query) ih
private theorem old_primitive (setup : Setup base KemSK) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    OldBounded (RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) 0 := by
  unfold RegistrationNativeBeaconFrontend.primitive
  apply old_program_zero
  intro lower
  cases lower with
  | inl other => exact old_sample _
  | inr other => exact old_kem _
private theorem old_agreement (setup : Setup base KemSK) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    OldBounded (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) 0 := by
  unfold RegistrationNativeBeaconFrontend.agreement
  apply old_bind _ _ 0 0 (old_update _)
  intro _
  cases query with
  | root request => exact old_pure _ _
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request => exact old_primitive setup owner oneTime _

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem lift_old (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) (cap : Nat)
    (bounded : OldBounded work cap) : Bounded (RegistrationNativeIdentityFrontend.liftOld work) cap := by
  intro owners env
  simp only [RegistrationNativeIdentityFrontend.liftOld, StateT.run, state_lift_apply, state_map_apply,
    simulateQ_map, Functor.map_map, isQueryBoundP_map_iff]
  apply (bounded [] env).simulateQ_of_step
  · intro query _active
    simp [RegistrationNativeIdentityFrontend.ambientLift]
  · intro query inactive
    simp only [RegistrationNativeIdentityFrontend.ambientLift, isQueryBoundP_query_iff]
    intro active
    apply False.elim (inactive ?_)
    cases query with
    | inl query => cases query with
      | inl coin => exact active
      | inr capability => cases capability <;> exact active
    | inr query => exact active

/-- Every actual SDK agreement callback is hash-free, including indexed KEM, local identity DH and the root KDF. -/
theorem agreement_bound (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    Bounded (RegistrationNativeIdentityFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) 0 := by
  by_cases ordinary : RegistrationNativeIdentityAgreementShape.Other query
  · rw [RegistrationNativeIdentityAgreementShape.exposed_other setup owner oneTime query ordinary]
    exact lift_old _ _ (old_agreement setup _ oneTime query)
  · cases query with
    | convertSecret role =>
        have localRole : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
        subst role
        exact bind_bound _ _ 0 0 (update_env_bound _) (fun _ => pure_bound _ _)
    | dh request =>
        rcases request with ⟨role, peer⟩
        have localRole : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
        subst role
        apply bind_bound _ _ 0 0 (update_env_bound _)
        intro _
        apply lift_free_bound
        simp [RegistrationNativeIdentityCallbacks.dh, RegistrationNativeIdentityInterface.staticDh, IsHash]
    | convertPublic key | generate role | encapsulate key | decapsulate ciphertext | root request => exact False.elim (ordinary trivial)

def IsRecordHash : RegistrationRecordPrimitives.Request → Prop
  | .hash _ => True
  | _ => False
instance : DecidablePred IsRecordHash := fun query => by cases query <;> simp only [IsRecordHash] <;> infer_instance

private theorem old_record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Request) :
    OldBounded (RegistrationNativeBeaconFrontend.record (n := n) (Auxiliary := Auxiliary) (mldsaSource := source) setup wire query)
      (if IsRecordHash query then 1 else 0) := by
  unfold RegistrationNativeBeaconFrontend.record
  rw [← Nat.zero_add (if IsRecordHash query then 1 else 0)]
  apply old_bind _ _ 0 _ (old_update _)
  intro _
  cases query with
  | hash transcript =>
      change OldBounded (do
        let digest ← RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes))
        pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) 1
      exact old_bind _ _ 1 0 (old_effect _) (fun _ => old_pure _ _)
  | rootKdf request | initialKdf request | ratchetKdf request | «seal» request | write request | openAead request => exact old_sample _

/-- The actual record interpreter charges only its literal commitment hash and preserves all other source primitive effects at zero shared-hash cost. -/
theorem record_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Request) :
    Bounded (RegistrationNativeIdentityFrontend.record (n := n) (Auxiliary := Auxiliary) (source := source) setup wire query)
      (if IsRecordHash query then 1 else 0) := lift_old _ _ (old_record setup wire query)
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishPrimitiveHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishPrimitiveHashBounds.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishPrimitiveHashBounds.agreement_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishPrimitiveHashBounds.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishPrimitiveHashBounds.record_bound
