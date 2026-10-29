-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedSafe
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource

/-! Actual incoming collection and terminal preparation perform no installation. This is a structural open-AST property: native callbacks use local coins, hash verification, indexed KEM and root preparation, while installation belongs only to the later paired material stage. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

abbrev NativeInstall (role : Role) := RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall (n := n) (KemSK := KemSK) role

private theorem sample_free (role : Role) (work : ProbComp Value) :
    (sample (n := n) (KemSK := KemSK) work).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  unfold sample
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, NativeInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, Install, InstallEnv, isQueryBoundP_query_iff]

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
        simp [primitive, RegistrationNativeKemInterface.beacon, indexed, NativeInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall,
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

theorem collect_free (role : Role) (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  unfold collect
  exact run_free role _ (prefix_free role setup owner oneTime authenticated) _ before

private theorem prepare_free (role : Role) (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (RegistrationBeaconReferenceCompiler.prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationBeaconReferenceCompiler.prepare, NativeInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]

private theorem authentication_free (role : Role) (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    (simulateQ (RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK))
      (simulateQ (RegistrationAuthenticationCompiler.callbacks crypto verify) work)).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;>
    simp [QueryImpl.compose, RegistrationAuthenticationCompiler.callbacks,
      RegistrationBeaconReferenceCompiler.effect,
      NativeInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, Install, InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem map_apply {State Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT State m Value) (before : State) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem agreement_free (role : Role) (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((RegistrationBeaconReferenceCompiler.agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationBeaconReferenceCompiler.agreement, StateT.run_bind]
  apply isQueryBoundP_bind (n := 0) (m := 0) (collect_free role setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free role (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending)

/-- Terminal movement, actual response authentication, collection and root preparation cannot install either record role. -/
theorem preparation_free (role : Role) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceCompiler.finishPreparation (n := n) setup source packet).run owner).run before).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationBeaconReferenceCompiler.finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
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
    (((RegistrationBeaconReferenceFinish.abort (n := n) (KemSK := KemSK) owner).run current).run before).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationBeaconReferenceFinish.abort, bind_pure_comp]
  simp [RegistrationBeaconReferenceCompiler.effect, NativeInstall, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, Install, InstallEnv, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix.collect_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix.preparation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix.preparation_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix.abort_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix.abort_free
