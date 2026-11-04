-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap
/-! Literal owner publication syntax with a stateful serializer attempts no Server or Beacon install. Source sampling, signing receipts, owner updates and every mutable writer result remain present; only the install query class is counted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeBeaconFrontend (Trusted Owner)
open RegistrationNativeG3MaterializedOrdinary (TrustedInstall)
open RegistrationNativePlatformGenericBundle (M Spec liftLegacy trustedLift)
variable {n : Nat} {I KemSK Auxiliary E A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def NativeFree (role : Role) (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) : Prop :=
  ∀ owners env, ((work.run owners).run env).IsQueryBoundP (TrustedInstall (KemSK := KemSK) role) 0
private theorem native_pure (role : Role) (value : A) : NativeFree role (pure value : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) :=
  fun _ _ => isQueryBoundP_pure _ _ _
private theorem native_bind (role : Role) (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (next : A → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary B)
    (prior : NativeFree role work) (later : ∀ value, NativeFree role (next value)) : NativeFree role (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (prior owners env) (fun result _ => later result.1.1 result.1.2 result.2)
private theorem native_effect (role : Role) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (free : ¬ RegistrationNativeSecretWordAtomInstallCaps.InstallEnv role query) :
    NativeFree role (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) query) := by
  intro owners env
  simp only [RegistrationNativeBeaconFrontend.effect, StateT.run_lift, StateT.run_map,
    bind_pure_comp, Functor.map_map, isQueryBoundP_map_iff]
  simp only [isQueryBoundP_query_iff, TrustedInstall]
  cases query with
  | inl coin => simp
  | inr capability => cases capability <;> simp_all [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]
private theorem native_sample (role : Role) (work : ProbComp A) :
    NativeFree role (RegistrationNativeBeaconFrontend.sample work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact native_pure role value
  | query_bind coin next ih =>
    simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_bind, simulateQ_spec_query]
    exact native_bind role _ _ (native_effect role _ (by simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])) ih
private theorem native_modify (role : Role)
    (change : RegistrationNativeBeaconFrontend.State source → RegistrationNativeBeaconFrontend.State source) :
    NativeFree role (modify change : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure]
  trivial
private theorem native_update (role : Role)
    (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    NativeFree role (RegistrationNativeBeaconFrontend.updateEnv change : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [RegistrationNativeBeaconFrontend.updateEnv, StateT.run_lift]
  trivial

theorem outgoing_free (role : Role) (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    NativeFree role (RegistrationNativeBeaconFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact native_effect role _ (by simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])
    | sign request payload digest => exact native_bind role _ _ (native_sample role _) (fun _ => native_bind role _ _ (native_update role _) (fun _ => native_pure role _))
  | inr request =>
    simp only [RegistrationNativeBeaconFrontend.outgoing]
    split
    · exact native_bind role _ _ (native_modify role _) (fun _ => native_pure role _)
    · exact native_pure role _

def Install (role : Role) : (Spec E n KemSK).Domain → Prop
  | .inl query => TrustedInstall (KemSK := KemSK) role query
  | .inr _ => False
instance (role : Role) : DecidablePred (Install (E := E) (n := n) (KemSK := KemSK) role) := fun query => by
  cases query <;> dsimp [Install] <;> infer_instance

def Free (role : Role) (work : M source Auxiliary (OracleComp (Spec E n KemSK)) A) : Prop :=
  ∀ owners env, ((work.run owners).run env).IsQueryBoundP (Install (E := E) (KemSK := KemSK) role) 0
private theorem pure_free (role : Role) (value : A) : Free role (pure value : M source Auxiliary (OracleComp (Spec E n KemSK)) A) :=
  fun _ _ => isQueryBoundP_pure _ _ _
private theorem bind_free (role : Role) (work : M source Auxiliary (OracleComp (Spec E n KemSK)) A)
    (next : A → M source Auxiliary (OracleComp (Spec E n KemSK)) B)
    (prior : Free role work) (later : ∀ value, Free role (next value)) : Free role (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (prior owners env) (fun result _ => later result.1.1 result.1.2 result.2)
private theorem legacy_free (role : Role) (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (free : NativeFree role work) : Free (E := E) role (liftLegacy trustedLift work) := by
  intro owners env
  unfold liftLegacy
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ 0 (free owners env)
  intro query
  simp only [trustedLift, isQueryBoundP_query_iff, Install]
  by_cases installed : TrustedInstall role query <;> simp [installed]
private theorem get_free (role : Role) : Free role (get : M source Auxiliary (OracleComp (Spec E n KemSK)) (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env
  simp only [StateT.run_get, StateT.run_pure]
  trivial

private abbrev Carrier (role : Role) (A : Type) :=
  {work : M source Auxiliary (OracleComp (Spec E n KemSK)) A // Free role work}
private abbrev carrierMonad (role : Role) : Monad (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) role) where
  pure value := ⟨pure value, pure_free role value⟩
  bind work next := ⟨work.val >>= fun value => (next value).val, bind_free role _ _ work.property (fun value => (next value).property)⟩

private theorem publication_free (role : Role) (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (encode : registration.SignedInitView → M source Auxiliary (OracleComp (Spec E n KemSK)) (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : ∀ packet, Free role (encode packet)) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Free role (RegistrationNativePlatformBeaconPublication.begin
      (fun query => liftLegacy trustedLift (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
      encode ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey) := by
  let _ := carrierMonad (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) role
  let _ : LawfulMonad (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) role) := LawfulMonad.mk' _
    (fun work => by apply Subtype.ext; exact bind_pure work.val)
    (fun value next => by apply Subtype.ext; exact pure_bind value (fun value => (next value).val))
    (fun work next rest => by apply Subtype.ext; exact bind_assoc work.val (fun value => (next value).val) (fun value => (rest value).val))
  let forget : ∀ {A : Type}, Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) role A → M source Auxiliary (OracleComp (Spec E n KemSK)) A := fun {_} work => work.val
  have hom : Cslib.IsMonadHom (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) role) (M source Auxiliary (OracleComp (Spec E n KemSK))) forget := .mk' (fun _ => rfl) (fun _ _ => rfl)
  let operations : QueryImpl RegistrationBeaconInitExecutor.Spec (Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) role) :=
    fun query => ⟨liftLegacy trustedLift (RegistrationNativeBeaconFrontend.outgoing setup source index owner query), legacy_free role _ (outgoing_free role setup index owner query)⟩
  let encoding : registration.SignedInitView → Carrier (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) role (RustM (core.option.Option (alloc.vec.Vec U8))) := fun packet => ⟨encode packet, writer packet⟩
  have kept := (RegistrationNativePlatformBeaconPublication.begin operations encoding ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey).property
  change Free role (forget (RegistrationNativePlatformBeaconPublication.begin operations encoding _ _ _ _ _)) at kept
  rw [RegistrationNativePlatformBeaconMap.begin hom] at kept
  exact kept

theorem bundle_free (role : Role) (setup : Setup base KemSK)
    (encode : registration.SignedInitView → M source Auxiliary (OracleComp (Spec E n KemSK)) (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : ∀ packet, Free role (encode packet)) (index : Nat) :
    Free role (RegistrationNativePlatformGenericBundle.bundle trustedLift setup source encode index) := by
  unfold RegistrationNativePlatformGenericBundle.bundle
  apply bind_free _ _ _ (get_free role)
  intro owners
  cases found : owners[index]? with
  | none => exact pure_free role _
  | some owner =>
    have finish (oneTime : PqxdhJointGapDh.ScalarBytes) := publication_free role setup index owner encode writer oneTime
    cases phase : owner.phase with
    | fresh | freshWithCoins scalar =>
      simp only [phase]
      apply bind_free _ _ _
      · first
        | exact legacy_free role _ (native_sample role _)
        | exact pure_free role _
      · intro oneTime
        apply bind_free _ _ _ (finish oneTime)
        intro published
        cases published with
        | fail error | div => exact pure_free role _
        | ok result => cases result with
          | Err previous => exact pure_free role _
          | Ok finished =>
            apply bind_free _ _ _ (legacy_free role _ (native_modify role _))
            intro _
            apply bind_free _ _ _ (legacy_free role _ (native_effect role _ (by simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])))
            intro _
            exact pure_free role _
    | initSent pending scalar | established completed | aborted previous =>
      simp only [phase]
      exact pure_free role _

private theorem encoder_free (role : Role) (view : registration.SignedInitView) :
    Free role (RegistrationNativePlatformGenericBundle.encoder (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) E view) := by
  intro owners env
  simp only [RegistrationNativePlatformGenericBundle.encoder, RegistrationNativePlatformGenericBundle.encoderWith,
    StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map, isQueryBoundP_map_iff]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativePlatformGenericBundle.writerLift, Install, isQueryBoundP_query_iff]

/-- The actual writer-taking source bundle is installation-free before any interpretation of its original allocation/serializer requests. -/
theorem program_free (role : Role) (setup : Setup base KemSK) (index : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativePlatformGenericBundle.program (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) E setup source index).run owners).run env).IsQueryBoundP
      (Install (E := E) (KemSK := KemSK) role) 0 :=
  bundle_free role setup _ (encoder_free role) index owners env
end BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree.outgoing_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree.outgoing_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree.bundle_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree.bundle_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree.program_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree.program_free
