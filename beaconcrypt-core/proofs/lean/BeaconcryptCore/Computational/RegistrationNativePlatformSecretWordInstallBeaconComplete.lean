-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconMaterial
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource
/-! The corrected Word material demand records its own reference before the actual first-record program. Missing material and all terminal aborts keep their literal public reply and full analysis state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationNativeSecretWordMessage (BeaconReady)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {I KemSK Auxiliary Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

noncomputable def compile (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Value) :=
  simulateQ (RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar) work

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before


private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  rw [bind_pure_comp]

theorem abort (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (env : EnvState Auxiliary) (value : RustM (Option Pqxdh.Bytes))
    (before : State) (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner *> pure value).run current).run env))).run before)) :
    result.1.1.1 = value ∧ result.2 = before := by
  cases scalar <;>
    simp only [compile, RegistrationNativeSecretWordAtomOwnerSource.routing, RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind, bind_pure_comp, StateT.run, map_apply, lift_apply,
      simulateQ_map, Functor.map_map,
      RegistrationNativeSecretWordInterface.effect, QueryImpl.compose, RegistrationNativeSecretWordOwners.ordinary,
      RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query, handler,
      RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish, map_apply, Functor.map_map, Prod.map_def, id_eq, support_map] at supported
  all_goals
    obtain ⟨reached, called, equal⟩ := supported
    cases equal
    constructor
    · rfl
    · rfl

private theorem effect_route (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeSecretWordAtomOwnerSource.routing (n := n) setup scalar ∘ₛ
      RegistrationNativeSecretWordInterface.effect = RegistrationNativePlatformSecretWordAtomEffects.env := by
  cases scalar with
  | none => rfl
  | some scalar =>
    funext query
    simp only [RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.apply_compose,
      RegistrationNativeSecretWordInterface.effect, simulateQ_spec_query, RegistrationNativeSecretWordOwners.ordinary,
      RegistrationNativePlatformSecretWordAtomEffects.env]

private theorem chosen_run (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (before : EnvState Auxiliary) :
    compile setup scalar (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer
      RegistrationNativeSecretWordInterface.effect owner ready choice).run current).run before) =
    simulateQ RegistrationNativePlatformSecretWordAtomEffects.env
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run before) := by
  unfold compile
  change simulateQ (RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar)
    (simulateQ RegistrationNativeSecretWordInterface.effect _) = _
  rw [← QueryImpl.simulateQ_compose, effect_route]

private theorem demand_run (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (message : RegistrationNativeSecretWordMessage.Message) :
    RegistrationNativeSecretWordAtomOwnerSource.routing (n := n) setup scalar (.inr (.inl (.inl message))) =
      (RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) := by
  cases scalar <;> rfl

/-- Every actual corrected material completion adds its own descriptor precisely on a successful returned application. -/
theorem complete_all (role : Role) (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : BeaconReady) (before : EnvState Auxiliary) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      (((RegistrationNativePlatformSecretWordFinish.complete crypto writer owner ready).run current).run before))).run trace)) :
    messages role result.2.events = messages role trace.events ++
      if role = .beacon ∧ present result.1.1.1 = true then [ready.reference] else [] := by
  simp only [compile, RegistrationNativePlatformSecretWordFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, RegistrationNativeSecretWordInterface.demand,
    simulateQ_bind, simulateQ_spec_query, demand_run, StateT.run_bind] at supported
  simp only [handler, StateT.run, RegistrationNativeSecretWordFrontendTrace.begin,
    RegistrationNativeSecretWordFrontendTrace.finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨choice, _actual, supported⟩ := supported
  cases choice with
  | none =>
    have ended := abort (n := n) setup scalar owner current before (.ok none)
      ⟨some ready.reference, trace.events ++ [RegistrationNativeSecretWordFrontendTrace.Event.demand ready.reference]⟩ result
      (by simpa only [compile, StateT.run] using supported)
    rw [ended.2, ended.1]
    simp only [present, Bool.false_eq_true, and_false, ite_false, messages,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil]
  | some choice =>
    change result ∈ support ((simulateQ handler (compile setup scalar
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationNativeSecretWordInterface.effect
        owner (ready.eval RegistrationNativeSecretWordMessage.zero) choice).run current).run before))).run
          ⟨some ready.reference, trace.events ++ [.demand ready.reference]⟩) at supported
    rw [chosen_run] at supported
    have counted := RegistrationNativePlatformSecretWordInstallBeaconMaterial.program_messages role crypto writer owner current
      (ready.eval RegistrationNativeSecretWordMessage.zero) choice before
      ⟨some ready.reference, trace.events ++ [.demand ready.reference]⟩ ready.reference rfl result supported
    simpa only [messages, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil] using counted

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete.abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete.abort
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete.complete_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete.complete_all
