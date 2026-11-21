-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedSafe
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps

/-! The actual native authentication, replay, indexed KEM collection and root preparation prefix cannot attempt either record installation. These structural bills close the native paired monitor on every failed and successful accept path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedServerPrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (Spec effect prepare indexed)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeSecretWordAtomOwnerInstallPrefix (NativeInstall)
variable (role : Role)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem environment_free (work : OracleComp (EnvEffects n) Value)
    (bounded : work.IsQueryBoundP (InstallEnv role) 0) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  by_cases charged : InstallEnv role query <;>
    simp [effect, NativeInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, charged, isQueryBoundP_query_iff]

private theorem old_backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : Environment) :
    (simulateQ (RegistrationNativeKemReferenceCompiler.lift (n := n) (KemSK := KemSK))
      ((RegistrationServerReferenceCompiler.backend setup checks query).run before)).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  change (simulateQ (RegistrationNativeKemReferenceCompiler.lift (n := n) (KemSK := KemSK))
    (simulateQ RegistrationServerReferenceCompiler.effect
      ((RegistrationWorldAgreementCompiler.compiler setup.source (RegistrationServerRoleBackend.localBackend setup checks) query).run before))).IsQueryBoundP
        (NativeInstall (KemSK := KemSK) role) 0
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeKemReferenceCompiler.lift (n := n) (KemSK := KemSK) ∘ₛ RegistrationServerReferenceCompiler.effect = effect := by
    funext request
    simp only [QueryImpl.compose, RegistrationServerReferenceCompiler.effect, simulateQ_spec_query,
      RegistrationNativeKemReferenceCompiler.lift, effect]
  rw [same]
  apply environment_free role
  simp only [RegistrationWorldAgreementCompiler.compiler, StateT.run, isQueryBoundP_map_iff]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationWorldCoinCompiler.envCoin, InstallEnv, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : Environment) :
    ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks query).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  cases query with
  | encapsulate key =>
      simp only [RegistrationNativeKemReferenceCompiler.backend, StateT.run, isQueryBoundP_map_iff]
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      intro request
      simp [indexed, NativeInstall, isQueryBoundP_query_iff]
  | _ => exact old_backend_free role setup checks _ before

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    ((simulateQ (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks) work).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible state
    exact impossible.elim
  · intro query _quiet state
    exact backend_free role setup checks query state

private theorem prefix_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
      RegistrationNativeKemReferenceCompiler.visit query).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first | exact backend_program_free role setup checks _ before | trivial

/-- The whole native Server collector, including the genuine indexed getter, has no installation callback. -/
theorem collect_free (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((RegistrationNativeKemReferenceCompiler.collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  unfold RegistrationNativeKemReferenceCompiler.collect
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query impossible state
    exact impossible.elim
  · intro query _quiet state
    exact prefix_free role setup checks query state
attribute [local irreducible] RegistrationAuthenticationExecutor.begin

private theorem authentication_free (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    (RegistrationAuthenticationCompiler.program (n := n) crypto verify pin packet).IsQueryBoundP (InstallEnv role) 0 := by
  unfold RegistrationAuthenticationCompiler.program
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationAuthenticationCompiler.callbacks, InstallEnv, isQueryBoundP_query_iff]

private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, NativeInstall, isQueryBoundP_query_iff]

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem agreement_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationServerOpenReferenceCompiler.agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free role setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some collected => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free role (n := n) (KemSK := KemSK) (RegistrationServerReferenceRoot.client authenticated.binding collected))

private theorem retain_free (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationServerOpenReferenceCompiler.retain, StateT.run]
  cases RegistrationServerMaterialFrontend.retain ready before with
  | fail error | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

private theorem after_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationServerOpenReferenceCompiler.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · simp only [StateT.run_bind]
      apply isQueryBoundP_bind (m := 0) (agreement_bound role setup checks packet authenticated before env)
      intro result _reached
      cases result.1.1 with
      | fail error | div => trivial
      | ok reply => cases reply with
        | none => trivial
        | some ready => exact retain_free role ready result.1.2 result.2
    · trivial

attribute [local irreducible] RegistrationAuthenticationCompiler.program

/-- All mandatory authentication and original replay/allocator failures precede installation and retain a zero bill. -/
theorem accept_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationServerOpenReferenceCompiler.accept, StateT.run_bind, StateT.run_get,
    StateT.run_lift, bind_pure_comp, pure_bind, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 0) (environment_free role _ (authentication_free role _ _ _ _))
  intro checked _
  cases checked with
  | fail error | div => trivial
  | ok checked =>
      rcases checked with ⟨events, verdict⟩
      cases verdict <;> first | exact after_bound role setup checks packet _ before env | trivial
end BeaconcryptCore.Computational.RegistrationNativePairedServerPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServerPrefix.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServerPrefix.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServerPrefix.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServerPrefix.accept_free
