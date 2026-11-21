-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativeInstallPredicate
import BeaconcryptCore.Computational.RegistrationNativeInstallRouting

/-! Actual response preparation makes no installation calls. Authentication forwards only its concrete hash callbacks, while ordinary key agreement and root preparation retain their original non-installation surface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation
open RegistrationBeaconReferenceCompiler
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeInstallPredicate (LocalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
variable (role : Role)

private theorem effect_free (work : OracleComp (EnvEffects n) Value)
    (bounded : work.IsQueryBoundP (InstallEnv role) 0) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  by_cases counted : InstallEnv role query <;>
    simp [effect, LocalInstall, Install, counted, isQueryBoundP_query_iff]

private theorem authentication_free (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    (simulateQ (RegistrationAuthenticationCompiler.callbacks (n := n) crypto verify) work).IsQueryBoundP (InstallEnv role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationAuthenticationCompiler.callbacks, InstallEnv,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem sample_free (work : ProbComp Value) :
    (sample (n := n) (KemSK := KemSK) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  unfold sample
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [effect, LocalInstall, Install, InstallEnv, isQueryBoundP_query_iff]

private theorem primitive_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    (primitive (n := n) setup owner oneTime query).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  unfold primitive
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query with
  | inl query => simpa only [other, ite_false] using (sample_free role (KemSK := KemSK) _)
  | inr query => simp [indexed, LocalInstall, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : EnvState Auxiliary) :
    ((backend (n := n) setup owner oneTime query).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift,
    bind_pure_comp, isQueryBoundP_map_iff]
  cases query <;> first | exact primitive_free role setup owner oneTime _ | trivial

private theorem backend_program_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : EnvState Auxiliary) :
    ((simulateQ (backend (n := n) setup owner oneTime) work).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    contradiction
  · intro query _ current
    exact backend_free role setup owner oneTime query current

private theorem prefix_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : EnvState Auxiliary) :
    ((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup owner oneTime) authenticated) visit query).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl]
  all_goals first | exact backend_program_free role setup owner oneTime _ before | trivial

/-- Every actual selected-owner prefix path has zero installation cost. -/
theorem collect_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  unfold collect
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query impossible
    contradiction
  · intro query _ current
    exact prefix_free role setup owner oneTime authenticated query current

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, LocalInstall, isQueryBoundP_query_iff]

private theorem agreement_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free role setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free role (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending)

/-- Actual response authentication and root preparation make no role installation. -/
theorem preparation_free (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup mlSource packet).run owner).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => trivial
  | freshWithCoins oneTime => trivial
  | established completed => trivial
  | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply isQueryBoundP_bind (m := 0) (effect_free role _ (authentication_free role _ _ _))
          intro accepted _
          cases accepted with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, map_apply, isQueryBoundP_map_iff] using
                  agreement_free role setup owner oneTime authenticated before

/-- The exact original native routed preparation is installation-free, ready for the same-trace typed finish proof. -/
theorem routed_preparation_free (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (before : EnvState Auxiliary) :
    (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
      (((finishPreparation (n := n) setup mlSource packet).run owner).run before)).IsQueryBoundP
        (RegistrationNativeInstallPredicate.GlobalInstall (KemSK := KemSK) role) 0 :=
  RegistrationNativeInstallRouting.local_bound role false _ 0
    (preparation_free role setup mlSource packet owner before)

end BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation.preparation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation.preparation_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation.routed_preparation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation.routed_preparation_free
