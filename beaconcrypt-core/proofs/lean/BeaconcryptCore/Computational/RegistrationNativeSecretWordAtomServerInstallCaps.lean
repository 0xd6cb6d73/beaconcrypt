-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler

/-! The actual opaque-word Server controller has one indexed encapsulation position. Authentication, replay, reservation and ordinary primitive failures add no encapsulation, and preparation follows that same getter without duplicating its word. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare localKem)
open RegistrationNativeSecretWordServerCompiler (backend ordinaryPrefix prefixImpl collect agreement retain afterAuthentication accept)
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
variable (role : Role)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem environment_free (work : OracleComp (EnvEffects n) Value)
    (bounded : work.IsQueryBoundP (InstallEnv role) 0) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  by_cases charged : InstallEnv role query <;>
    simp [effect, LocalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, charged, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : Environment) :
    ((backend (n := n) setup checks query).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply environment_free role
  simp only [RegistrationWorldAgreementCompiler.compiler, StateT.run, isQueryBoundP_map_iff]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationWorldCoinCompiler.envCoin, InstallEnv, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationAuthenticationExecutor.begin

private theorem authentication_free (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    (RegistrationAuthenticationCompiler.program (n := n) crypto verify pin packet).IsQueryBoundP (InstallEnv role) 0 := by
  unfold RegistrationAuthenticationCompiler.program
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationAuthenticationCompiler.callbacks, InstallEnv, isQueryBoundP_query_iff]

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    ((simulateQ (backend (n := n) setup checks) work).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible state
    exact impossible.elim
  · intro query _quiet state
    exact backend_free role setup checks query state

private theorem ordinary_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((ordinaryPrefix (n := n) setup checks query).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  cases query <;> simp only [ordinaryPrefix, PqxdhServerStaticDhSource.prefixImpl,
    RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact backend_program_free role setup checks _ before
    | trivial

private theorem prefix_bound (setup : Setup base KemSK) (checks : Checks)
    (query : (RegistrationNativeSecretWordServerCollect.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((prefixImpl (n := n) setup checks query).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role)
      0 := by
  cases query <;> simp only [prefixImpl]
  all_goals first
    | exact ordinary_free role setup checks _ before
    | (simp only [StateT.run]; split
       · simp [localKem, LocalInstall, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
       · trivial)

/-- The actual current-environment collector performs no role installation, including all failed getters. -/
theorem collect_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  unfold RegistrationNativeSecretWordServerCompiler.collect
  apply (isQueryBoundP_false (RegistrationNativeSecretWordServerCollect.collect (RegistrationRootInput.verified packet authenticated)) 0).simulateQ_run_of_step
  · intro query impossible state
    exact impossible.elim
  · intro query _quiet state
    exact prefix_bound role setup checks query state

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, LocalInstall, isQueryBoundP_query_iff]

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem agreement_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_bound role setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some collected => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free role (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected))

private theorem retain_free (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before with
  | fail error | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

private theorem after_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
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

set_option maxRecDepth 4096 in
/-- Actual authentication, replay, collection and root preparation perform no role installation. -/
theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  rw [RegistrationNativeSecretWordTargetServerReceipt.accept_program_source]
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 0) (environment_free role _ (authentication_free role _ _ _ _))
  intro checked _
  cases checked with
  | fail error | div => trivial
  | ok checked =>
      rcases checked with ⟨events, verdict⟩
      cases verdict <;> first
        | exact after_bound role setup checks packet _ before env
        | trivial

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps.collect_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps.accept_bound
