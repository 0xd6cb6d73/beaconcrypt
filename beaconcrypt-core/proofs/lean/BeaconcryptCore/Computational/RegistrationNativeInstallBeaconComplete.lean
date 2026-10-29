-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallTrace
import BeaconcryptCore.Computational.RegistrationNativeInstallAdmitted
import BeaconcryptCore.Computational.RegistrationNativeInstallTrace
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion

/-! The actual Beacon material stage emits raw Common callbacks. Its own demand establishes the exact descriptor before any installation attempt; publication/opening failures and stale prior trace metadata remain present. No Common-compiler environment is substituted for this direct paired controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeRelatedFamily (Message)
open RegistrationBeaconReferenceRoot (Ready)
open RegistrationNativePublicFrontend (Spec liftLocal)
open RegistrationNativeG2Trace (State handler begin finish)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallInsert (success)
open RegistrationNativeInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
variable {n : Nat} {KemSK Value Auxiliary : Type}

noncomputable def compile (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) : OracleComp (Spec n KemSK) Value :=
  simulateQ (liftLocal false) work


private theorem paired_source (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    compile (KemSK := KemSK) (simulateQ RegistrationBeaconReferenceFinish.service work) =
      simulateQ RegistrationNativePairedMaterialSource.nativeLift work := by
  rw [compile, ← QueryImpl.simulateQ_compose]
  have same : liftLocal (n := n) (KemSK := KemSK) false ∘ₛ RegistrationBeaconReferenceFinish.service =
      RegistrationNativePairedMaterialSource.nativeLift (n := n) (KemSK := KemSK) := by
    funext query
    simp only [QueryImpl.compose, RegistrationBeaconReferenceFinish.service, simulateQ_spec_query,
      liftLocal, RegistrationNativePairedMaterialSource.nativeLift]
  rw [same]

private theorem compile_pure (value : Value) : compile (n := n) (KemSK := KemSK) (pure value) = pure value := by
  simp only [compile, simulateQ_pure]

private theorem compile_bind {Result : Type}
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (next : Value → OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Result) :
    compile (KemSK := KemSK) (work >>= next) = (compile work >>= fun value => compile (next value)) := by
  simp only [compile, simulateQ_bind]

private theorem map_apply {Private Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT Private m Value) (before : Private) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private noncomputable def after {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (published : RustM RegistrationNativePairedBeaconService.Result) :
    OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)
      ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) :=
  match published with
  | .fail error => (((RegistrationBeaconReferenceFinish.abort owner *> pure (.fail error)).run current).run env)
  | .div => (((RegistrationBeaconReferenceFinish.abort owner *> pure .div).run current).run env)
  | .ok (.Err _) => (((RegistrationBeaconReferenceFinish.abort owner *> pure (.ok none)).run current).run env)
  | .ok (.Ok completed) => pure ((.ok (some (TranscriptAuthParts.absSlice completed.application)),
      { current with phase := .established completed }), env)

private theorem complete_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : Ready) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run env) = (do
      let published ← simulateQ (RegistrationBeaconReferenceFinish.service (n := n) (KemSK := KemSK))
        (RegistrationNativePairedBeaconService.admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference)
      after (KemSK := KemSK) owner current env published) := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
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
      (((RegistrationBeaconReferenceFinish.abort owner).run current).run env)).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationBeaconReferenceFinish.abort, bind_pure_comp]
  simp [compile, RegistrationBeaconReferenceCompiler.effect, liftLocal,
    GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
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

def present {Value : Type} : RustM (Option Value) → Bool
  | .ok (some _) => true
  | _ => false

private theorem collapse_present (published : RustM RegistrationNativePairedBeaconService.Result) :
    success published = present (collapse published) := by
  cases published with
  | fail error | div => rfl
  | ok outcome => cases outcome <;> rfl

/-- The actual successful direct Beacon completion adds its own Ready descriptor once in the Beacon role and none in the Server role. -/
theorem complete (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : Ready) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner mlSource) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK)
      (((RegistrationBeaconReferenceFinish.complete source owner ready).run current).run env))).run trace))
    :
    messages role result.2.events = messages role trace.events ++ if role = .beacon ∧ present result.1.1.1 = true then [ready.reference] else [] := by
  rw [complete_run, compile_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨published, material, settled⟩ := supported
  have value := after_value owner current env published.1 published.2 result settled
  have first := RegistrationNativeInstallAdmitted.beacon role source owner.worldOwner owner.pin.binding.identity_key_id
    ready.descriptor ready.reference trace published (by simpa only [paired_source] using material)
  have last := RegistrationNativeInstallTrace.free role _
    (after_free role owner current env published.1) published.2 result settled
  rw [last, first, value, collapse_present]
end BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete.complete
