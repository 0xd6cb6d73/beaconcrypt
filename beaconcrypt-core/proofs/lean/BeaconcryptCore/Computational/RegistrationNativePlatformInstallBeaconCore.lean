-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconSafe
import BeaconcryptCore.Computational.RegistrationNativeInstallAfter
import BeaconcryptCore.Computational.RegistrationNativeInstallTrace
/-! Exact successful descriptor accounting for the actual assigned-ID Beacon installation. The raw source prefix and native failure outcomes retain their original execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore
open PqxdhRecordLiftInterface (EnvEffects Role KernelRef)
open RegistrationNativeG2Trace (State handler)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallInsert (success)
open RegistrationNativeRelatedFamily (Message)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativePublicFrontend (effect)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
variable {n : Nat} {KemSK Auxiliary A : Type} {source : RegistrationNativeMldsa.Source}

/-- Installation-free actual Env trees leave the full concrete G2 analysis trace unchanged. -/
theorem neutral (work : OracleComp (EnvEffects n) A)
    (free : ∀ role, work.IsQueryBoundP (InstallEnv role) 0) (before : State) :
    (simulateQ handler (simulateQ (effect (KemSK := KemSK)) work)).run before =
      (fun value => (value, before)) <$> simulateQ effect work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    have counted := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (free role)
    have absent : ∀ role, ¬ InstallEnv role query := fun role => (counted role).1.resolve_right (by omega)
    have leaf : (simulateQ handler (effect (KemSK := KemSK) query)).run before =
        (fun reply => (reply, before)) <$> effect query := by
      cases query with
      | inl coin => rfl
      | inr capability => cases capability with
        | installServer key binding kernel => exact (absent .server rfl).elim
        | installBeacon owner shell kernel => exact (absent .beacon rfl).elim
        | _ => rfl
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, leaf, bind_map_left, map_bind]
    apply bind_congr
    intro reply
    exact ih reply (fun role => by simpa only [Nat.zero_sub, ite_self] using (counted role).2 reply)

/-- The literal corrected post-opening controller installs its completed assigned identifier once exactly on native success. -/
theorem after_messages (role : Role) (owner : Nat)
    (kernel : registration.CompletedBeacon → KernelRef n) (opened : RustM RegistrationBeaconRecordExecutor.Result)
    (before : State) (message : Message) (active : before.current = some message)
    (result : RustM RegistrationNativePairedBeaconService.Result × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effect (KemSK := KemSK))
      (RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel opened))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .beacon ∧ success result.1 = true then [message] else [] := by
  cases opened with
  | fail error | div =>
    change result ∈ support (pure (_, before) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) at supported
    rw [mem_support_pure_iff] at supported
    cases supported
    simp only [success, Bool.false_eq_true, and_false, ite_false, List.append_nil]
  | ok outcome => cases outcome with
    | Err aborted =>
      change result ∈ support (pure (_, before) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) at supported
      rw [mem_support_pure_iff] at supported
      cases supported
      simp only [success, Bool.false_eq_true, and_false, ite_false, List.append_nil]
    | Ok completed =>
      exact RegistrationNativeInstallInsert.beacon role owner completed.binding.assigned_key_id kernel completed before message active result supported

private theorem after_run (owner : Nat) (kernel : registration.CompletedBeacon → KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) (before : EnvState Auxiliary) :
    (RegistrationNativePlatformPairedBeaconService.after
      (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner kernel result).run before =
      (fun reply => (reply, before)) <$> RegistrationNativePlatformPairedBeaconService.after
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel result := by
  cases result with
  | fail error | div => simp only [RegistrationNativePlatformPairedBeaconService.after, StateT.run_pure, map_pure]
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePlatformPairedBeaconService.after, StateT.run_pure, map_pure]
    | Ok completed =>
      simp only [RegistrationNativePlatformPairedBeaconService.after, StateT.run, QueryImpl.ofLift]
      rfl

/-- The actual source opening prefix is neutral, followed by the single native insertion selected by its literal result. -/
theorem stage_messages (role : Role) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (owner : Nat)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (choice : RegistrationNativePairedChoice.Choice n)
    (envBefore : EnvState Auxiliary) (before : State) (message : Message) (active : before.current = some message)
    (result : (RustM RegistrationNativePairedBeaconService.Result × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effect (KemSK := KemSK))
      ((RegistrationNativePlatformPairedBeaconOwner.publicBranch crypto
        (RegistrationBeaconChargedSource.primitive
          (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
        (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _))
        owner descriptor choice).run envBefore))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .beacon ∧ success result.1.1 = true then [message] else [] := by
  cases choice <;>
    simp only [RegistrationNativePlatformPairedBeaconOwner.publicBranch,
      RegistrationNativePlatformPairedBeaconOwner.knownStage,
      RegistrationNativePlatformPairedBeaconOwner.publicHidden,
      RegistrationNativePlatformPairedBeaconOwner.hiddenStage, StateT.run_bind,
      simulateQ_bind, StateT.run_bind] at supported
  all_goals
    rw [neutral _ (fun role => RegistrationNativePlatformPairedBeaconRawFree.program_free crypto writer role _ envBefore)] at supported
    simp only [bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨opened, _called, continued⟩ := supported
    rw [after_run] at continued
    simp only [simulateQ_map, StateT.run_map, support_map] at continued
    obtain ⟨finished, actual, equal⟩ := continued
    cases equal
    exact after_messages role owner _ opened.1 before message active finished actual

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore.neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore.neutral
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore.after_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore.after_messages

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore.stage_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconCore.stage_messages
