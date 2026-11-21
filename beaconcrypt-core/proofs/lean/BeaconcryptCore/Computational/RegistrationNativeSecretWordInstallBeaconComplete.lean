-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallAdmitted
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial

/-! The actual Beacon material stage emits raw Common callbacks. Its own demand establishes the exact descriptor before any installation attempt; publication/opening failures and stale prior trace metadata remain present. No Common-compiler environment is substituted for this direct paired controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal paired common)
open RegistrationNativeSecretWordFrontendTrace (State handler begin finish)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeSecretWordInstallInsert (success)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
variable {n : Nat} {KemSK Value Auxiliary : Type}

noncomputable def compile (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value) : OracleComp (Spec n KemSK) Value :=
  simulateQ (liftLocal false) (simulateQ paired work)

private theorem compile_pure (value : Value) : compile (n := n) (KemSK := KemSK) (pure value) = pure value := by
  simp only [compile, simulateQ_pure]

private theorem compile_bind {Result : Type}
    (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value)
    (next : Value → OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Result) :
    compile (KemSK := KemSK) (work >>= next) = (compile work >>= fun value => compile (next value)) := by
  simp only [compile, simulateQ_bind]

private theorem map_apply {Private Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT Private m Value) (before : Private) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private noncomputable def after {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (published : RustM RegistrationNativePairedBeaconService.Result) :
    OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n)
      ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) :=
  match published with
  | .fail error => (((RegistrationNativeSecretWordBeaconMaterial.abort owner *> pure (.fail error)).run current).run env)
  | .div => (((RegistrationNativeSecretWordBeaconMaterial.abort owner *> pure .div).run current).run env)
  | .ok (.Err _) => (((RegistrationNativeSecretWordBeaconMaterial.abort owner *> pure (.ok none)).run current).run env)
  | .ok (.Ok completed) => pure ((.ok (some (TranscriptAuthParts.absSlice completed.application)),
      { current with phase := .established completed }), env)

private theorem complete_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : BeaconReady) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner ready).run current).run env) = (do
      let published ← RegistrationNativeSecretWordBeaconMaterial.admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference
      after owner current env published) := by
  simp only [RegistrationNativeSecretWordBeaconMaterial.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply bind_congr
  intro published
  cases published with
  | fail error | div => rfl
  | ok published => cases published <;> rfl

private theorem abort_free (role : Role) {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativeSecretWordBeaconMaterial.abort owner).run current).run env)).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordBeaconMaterial.abort, bind_pure_comp]
  simp [compile, RegistrationNativeSecretWordBeaconMaterial.effect, paired, liftLocal,
    GlobalInstall, Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
    isQueryBoundP_query_iff, isQueryBoundP_map_iff]

private theorem after_free (role : Role) {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (published : RustM RegistrationNativePairedBeaconService.Result) :
    (compile (n := n) (KemSK := KemSK) (after owner current env published)).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  cases published with
  | fail error | div =>
      simpa only [after, seqRight_eq_bind, bind_pure_comp, StateT.run_map, StateT.run, map_apply,
        compile, simulateQ_map, isQueryBoundP_map_iff] using abort_free role (n := n) (KemSK := KemSK) owner current env
  | ok published => cases published with
    | Err rejected =>
        simpa only [after, seqRight_eq_bind, bind_pure_comp, StateT.run_map, StateT.run, map_apply,
          compile, simulateQ_map, isQueryBoundP_map_iff] using abort_free role (n := n) (KemSK := KemSK) owner current env
    | Ok completed => trivial


private def collapse : RustM RegistrationNativePairedBeaconService.Result → RustM (Option Pqxdh.Bytes)
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err _) => .ok none
  | .ok (.Ok completed) => .ok (some (TranscriptAuthParts.absSlice completed.application))

private theorem after_value {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (published : RustM RegistrationNativePairedBeaconService.Result) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK) (after owner current env published))).run trace)) :
    result.1.1.1 = collapse published := by
  cases published with
  | fail error | div =>
      simp only [after, seqRight_eq_bind, bind_pure_comp, StateT.run, map_apply,
        compile, simulateQ_map, support_map] at supported
      obtain ⟨reached, _called, equal⟩ := supported
      cases equal
      rfl
  | ok outcome => cases outcome with
    | Err aborted =>
        simp only [after, seqRight_eq_bind, bind_pure_comp, StateT.run, map_apply,
          compile, simulateQ_map, support_map] at supported
        obtain ⟨reached, _called, equal⟩ := supported
        cases equal
        rfl
    | Ok completed =>
        simp only [after, compile, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl

private theorem collapse_success (published : RustM RegistrationNativePairedBeaconService.Result)
    (application : Pqxdh.Bytes) (successful : collapse published = .ok (some application)) : success published = true := by
  cases published with
  | fail error | div => cases successful
  | ok outcome => cases outcome with
    | Err aborted => cases successful
    | Ok completed => rfl

/-- The actual successful direct Beacon completion adds its own Ready descriptor once in the Beacon role and none in the Server role. -/
theorem complete (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : BeaconReady) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner mlSource) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativeSecretWordBeaconMaterial.complete source owner ready).run current).run env))).run trace))
    (application : Pqxdh.Bytes) (successful : result.1.1.1 = .ok (some application)) :
    messages role result.2.events = messages role trace.events ++ if role = .beacon then [ready.reference] else [] := by
  rw [complete_run, compile_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨published, material, settled⟩ := supported
  have value := after_value owner current env published.1 published.2 result settled
  have succeeded := collapse_success published.1 application (value.symm.trans successful)
  have first := RegistrationNativeSecretWordInstallAdmitted.beacon role source owner.worldOwner owner.pin.binding.identity_key_id
    ready.descriptor ready.reference trace published (by simpa only [compile, QueryImpl.simulateQ_compose, RegistrationNativePairedMaterialSource.wordLift] using material)
  have last := RegistrationNativeSecretWordInstallTrace.free role _
    (after_free role owner current env published.1) published.2 result settled
  rw [last, first]
  simp only [succeeded, and_true]
private theorem collapse_present (published : RustM RegistrationNativePairedBeaconService.Result) :
    success published = RegistrationNativeInstallBeaconComplete.present (collapse published) := by
  cases published with
  | fail error | div => rfl
  | ok outcome => cases outcome <;> rfl

/-- Every direct Beacon completion has the exact successful descriptor suffix of its literal public reply. -/
theorem complete_all (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : BeaconReady) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner mlSource) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativeSecretWordBeaconMaterial.complete source owner ready).run current).run env))).run trace)) :
    messages role result.2.events = messages role trace.events ++
      if role = .beacon ∧ RegistrationNativeInstallBeaconComplete.present result.1.1.1 = true then [ready.reference] else [] := by
  rw [complete_run, compile_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨published, material, settled⟩ := supported
  have value := after_value owner current env published.1 published.2 result settled
  have first := RegistrationNativeSecretWordInstallAdmitted.beacon role source owner.worldOwner owner.pin.binding.identity_key_id
    ready.descriptor ready.reference trace published (by simpa only [compile, QueryImpl.simulateQ_compose, RegistrationNativePairedMaterialSource.wordLift] using material)
  have last := RegistrationNativeSecretWordInstallTrace.free role _
    (after_free role owner current env published.1) published.2 result settled
  rw [last, first, collapse_present, ← value]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete.complete_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete.complete_all
