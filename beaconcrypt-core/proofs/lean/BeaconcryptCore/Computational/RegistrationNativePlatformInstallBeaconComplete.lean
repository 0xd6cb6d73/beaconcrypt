-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconMaterial
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter
/-! The corrected material demand records its own reference before the actual first-record program. Missing material and all terminal aborts keep their literal public reply and full analysis state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconComplete
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeG2Trace (State handler)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationBeaconReferenceRoot (Ready)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {I KemSK Auxiliary Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

noncomputable def compile (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) :=
  simulateQ (RegistrationNativePublicFrontend.liftLocal false) work

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before


private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  rw [bind_pure_comp]

theorem abort (owner current : SelectedOwner source) (env : EnvState Auxiliary) (value : RustM (Option Pqxdh.Bytes))
    (before : State) (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationBeaconReferenceCompiler.effect owner *> pure value).run current).run env))).run before)) :
    result.1.1.1 = value ∧ result.2 = before := by
  simp only [compile, RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind, bind_pure_comp, StateT.run, map_apply, lift_apply,
      simulateQ_map, Functor.map_map,
      RegistrationBeaconReferenceCompiler.effect, RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query, handler,
      RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish, map_apply, Functor.map_map, Prod.map_def, id_eq, support_map] at supported
  all_goals
    obtain ⟨reached, called, equal⟩ := supported
    cases equal
    constructor
    · rfl
    · rfl

private theorem effect_route :
    RegistrationNativePublicFrontend.liftLocal (n := n) (KemSK := KemSK) false ∘ₛ
      RegistrationBeaconReferenceCompiler.effect = RegistrationNativePublicFrontend.effect := by
  funext query
  rfl

private theorem chosen_run (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (before : EnvState Auxiliary) :
    compile (KemSK := KemSK) (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer
      RegistrationBeaconReferenceCompiler.effect owner ready choice).run current).run before) =
    simulateQ RegistrationNativePublicFrontend.effect
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run before) := by
  unfold compile
  change simulateQ (RegistrationNativePublicFrontend.liftLocal false)
    (simulateQ RegistrationBeaconReferenceCompiler.effect _) = _
  rw [← QueryImpl.simulateQ_compose, effect_route]

private theorem demand_run (message : RegistrationNativeRelatedFamily.Message) :
    RegistrationNativePublicFrontend.liftLocal (n := n) (KemSK := KemSK) false (.inr (.inl (.inl message))) =
      (RegistrationNativePublicFrontend.Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) := by
  rfl

/-- Every actual corrected material completion adds its own descriptor precisely on a successful returned application. -/
theorem complete_all (role : Role) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : Ready) (before : EnvState Auxiliary) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer RegistrationBeaconReferenceCompiler.effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run before))).run trace)) :
    messages role result.2.events = messages role trace.events ++
      if role = .beacon ∧ present result.1.1.1 = true then [ready.reference] else [] := by
  simp only [compile, RegistrationNativePlatformBeaconMaterialFrontend.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, RegistrationNativePlatformBeaconMaterialInterpreter.demand,
    simulateQ_bind, simulateQ_spec_query, demand_run, StateT.run_bind] at supported
  simp only [handler, StateT.run, RegistrationNativeG2Trace.begin,
    RegistrationNativeG2Trace.finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨choice, _actual, supported⟩ := supported
  cases choice with
  | none =>
    have ended := abort (n := n) owner current before (.ok none)
      ⟨some ready.reference, trace.events ++ [RegistrationNativeG2Trace.Event.demand ready.reference]⟩ result
      (by simpa only [compile, StateT.run] using supported)
    rw [ended.2, ended.1]
    simp only [present, Bool.false_eq_true, and_false, ite_false, messages,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil]
  | some choice =>
    change result ∈ support ((simulateQ handler (compile (KemSK := KemSK)
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationBeaconReferenceCompiler.effect
        owner ready choice).run current).run before))).run
          ⟨some ready.reference, trace.events ++ [.demand ready.reference]⟩) at supported
    rw [chosen_run] at supported
    have counted := RegistrationNativePlatformInstallBeaconMaterial.program_messages role crypto writer owner current
      ready choice before
      ⟨some ready.reference, trace.events ++ [.demand ready.reference]⟩ ready.reference rfl result supported
    simpa only [messages, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil] using counted

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconComplete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconComplete.abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconComplete.abort
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconComplete.complete_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconComplete.complete_all
