-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallPredicate
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource

/-! Actual incoming collection and terminal preparation perform no installation. This is a structural open-AST property: native callbacks use local coins, hash verification, indexed KEM and root preparation, while installation belongs only to the later paired material stage. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

def NativeInstall (role : Role) : (Spec n KemSK).Domain → Prop
  | .inr (.inl (.inr query)) => Install role query
  | _ => False
instance (role : Role) : DecidablePred (NativeInstall (n := n) (KemSK := KemSK) role) := fun query => by
  rcases query with message | (message | common) | kem
  · exact isFalse id
  · exact isFalse id
  · exact inferInstanceAs (Decidable (Install role common))
  · exact isFalse id

private theorem sample_free (role : Role) (work : ProbComp Value) :
    (sample (n := n) (KemSK := KemSK) work).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  unfold sample
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, NativeInstall, Install, InstallEnv, isQueryBoundP_query_iff]

private theorem primitive_free (role : Role) (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    (primitive (n := n) setup owner oneTime query).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  cases query with
  | convertPublic key | convertSecret secretRole | generate ephemeralRole | dh request =>
      simpa only [primitive, RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        simulateQ_spec_query, other] using sample_free role (n := n) (KemSK := KemSK) _
  | encapsulate key => simp only [primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]; trivial
  | decapsulate ciphertext => cases ciphertext with
    | none => simp only [primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]; trivial
    | some ciphertext =>
        simp [primitive, RegistrationNativeKemInterface.beacon, indexed, NativeInstall,
          isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem backend_free (role : Role) (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : EnvState Auxiliary) :
    ((backend (n := n) setup owner oneTime query).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift,
    bind_pure_comp, isQueryBoundP_map_iff]
  cases query <;> first | exact primitive_free role setup owner oneTime _ | trivial

private theorem run_free {Index State Result : Type} {spec : OracleSpec Index}
    (role : Role) (implementation : QueryImpl spec (StateT State (OracleComp (Spec n KemSK))))
    (step : ∀ query before, ((implementation query).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0)
    (work : OracleComp spec Result) (before : State) :
    ((simulateQ implementation work).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact isQueryBoundP_bind (n := 0) (m := 0) (step query before) (fun result _ => ih result.1 result.2)

private theorem prefix_free (role : Role) (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : EnvState Auxiliary) :
    ((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup owner oneTime) authenticated) visit query).run before).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl]
  all_goals first
    | exact run_free role _ (backend_free role setup owner oneTime) _ before
    | trivial

private theorem native_collect_free (role : Role) (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  unfold collect
  exact run_free role _ (prefix_free role setup owner oneTime authenticated) _ before

private theorem realize_bound (role : Role) (work : OracleComp (Spec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (NativeInstall (KemSK := KemSK) role) cap) :
    (simulateQ (RegistrationNativeSecretWordServerSource.realize RegistrationNativeSecretWordMessage.zero) work).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  rcases query with message | (message | common) | (other | (pool | key))
  all_goals try cases pool
  all_goals simp [RegistrationNativeSecretWordServerSource.realize, RegistrationNativeSecretWordInterface.prepare,
    RegistrationNativeSecretWordInterface.demand, RegistrationNativeSecretWordInterface.common,
    RegistrationNativeSecretWordInterface.localKem, NativeInstall, LocalInstall,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  all_goals intro counted; rw [ite_eq_left counted]; decide

/-- The actual symbolic incoming collector has no installation query on any optional or metadata-admission branch. -/
theorem collect_free (role : Role) (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((RegistrationNativeSecretWordBeaconCompiler.collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  have bounded := realize_bound (n := n) role _ 0 (native_collect_free (n := n) role setup owner oneTime authenticated before)
  rw [RegistrationNativeSecretWordBeaconSource.collector_source] at bounded
  exact (isQueryBoundP_map_iff _ _ _).mp bounded

private theorem prepare_free (role : Role) (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
    (simulateQ (RegistrationNativeSecretWordInterface.prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeSecretWordInterface.prepare, LocalInstall, isQueryBoundP_query_iff]

private theorem authentication_free (role : Role) (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    (simulateQ (RegistrationNativeSecretWordInterface.effect (n := n) (KemSK := KemSK))
      (simulateQ (RegistrationAuthenticationCompiler.callbacks crypto verify) work)).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;>
    simp [QueryImpl.compose, RegistrationAuthenticationCompiler.callbacks,
      RegistrationNativeSecretWordInterface.effect,
      LocalInstall, Install, InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem map_apply {State Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT State m Value) (before : State) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem agreement_free (role : Role) (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((RegistrationNativeSecretWordBeaconCompiler.agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement, StateT.run_bind]
  apply isQueryBoundP_bind (n := 0) (m := 0) (collect_free role setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free role (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)

/-- Terminal movement, actual response authentication, collection and root preparation cannot install either record role. -/
theorem preparation_free (role : Role) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.finishPreparation (n := n) setup source packet).run owner).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply isQueryBoundP_bind (n := 0) (m := 0) (authentication_free role setup.source.crypto source.verify _)
          intro accepted _
          cases accepted with
          | fail error | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, map_apply, isQueryBoundP_map_iff] using
                  agreement_free role setup owner oneTime authenticated before

/-- Actual owner abort only advances its public phase and attempts no installation. -/
theorem abort_free (role : Role) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.abort (n := n) (KemSK := KemSK) owner).run current).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.abort, bind_pure_comp]
  simp [RegistrationNativeSecretWordInterface.effect, LocalInstall, Install, InstallEnv, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix.collect_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free
