-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete
/-! Exact successful Beacon handle receipts follow the literal insertion reply. The actual first-record prefix is installation-free and every refusal keeps its private effects without adding a successful public handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles
open PqxdhRecordLiftInterface (Role EnvEffects KernelRef)
open PqxdhDeploymentInterface (Handle)
open RegistrationNativePlatformRecordPartnerSnapshotHandles (handler update effects_free)
open RegistrationNativeSecretWordInstallInsert (success)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {KemSK Auxiliary : Type}
local notation "effects" => RegistrationNativePairedCompile.effects (n := n) (KemSK := KemSK)

/-- Actual Beacon insertion appends its own physical owner handle exactly when its original result succeeds. -/
theorem service_after (role : Role) (owner : Nat) (kernel : registration.CompletedBeacon → KernelRef n)
    (outcome : RustM RegistrationBeaconRecordExecutor.Result) (before : List Handle)
    (result : RustM RegistrationNativePairedBeaconService.Result × List Handle)
    (supported : result∈support ((simulateQ (handler role) (simulateQ effects
      (RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel outcome))).run before)) :
    result.2=before++if role=.beacon ∧ success result.1=true then [.owner owner] else [] := by
  cases outcome with
  | fail error | div =>
      simp only [RegistrationNativePlatformPairedBeaconService.after,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      subst result
      simp [success]
  | ok result => cases result with
    | Err previous =>
        simp only [RegistrationNativePlatformPairedBeaconService.after,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
        subst result
        simp [success]
    | Ok completed =>
        simp only [RegistrationNativePlatformPairedBeaconService.after,QueryImpl.ofLift,simulateQ_bind,
          simulateQ_spec_query,RegistrationNativePairedCompile.effects] at supported
        rw [StateT.run_bind] at supported
        simp only [handler,StateT.run,bind_map_left,mem_support_bind_iff] at supported
        obtain ⟨installed,_queried,continued⟩ := supported
        simp only [simulateQ_pure] at continued
        cases continued
        cases role <;> cases installed <;> simp [update,success]

private theorem after_run (owner : Nat) (kernel : registration.CompletedBeacon → KernelRef n)
    (outcome : RustM RegistrationBeaconRecordExecutor.Result) (env : EnvState Auxiliary) :
    (RegistrationNativePlatformPairedBeaconService.after
      (fun query=>StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner kernel outcome).run env=
      (fun reply=>(reply,env)) <$>
        RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel outcome := by
  cases outcome with
  | fail error | div => simp only [RegistrationNativePlatformPairedBeaconService.after,StateT.run_pure,map_pure]
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePlatformPairedBeaconService.after,StateT.run_pure,map_pure]
    | Ok completed =>
        simp only [RegistrationNativePlatformPairedBeaconService.after,StateT.run,QueryImpl.ofLift]
        rfl

/-- The same handle receipt retains the complete current record-request environment. -/
theorem after_state (role : Role) (owner : Nat) (kernel : registration.CompletedBeacon → KernelRef n)
    (outcome : RustM RegistrationBeaconRecordExecutor.Result) (env : EnvState Auxiliary) (before : List Handle)
    (result : (RustM RegistrationNativePairedBeaconService.Result × EnvState Auxiliary) × List Handle)
    (supported : result∈support ((simulateQ (handler role) (simulateQ effects
      ((RegistrationNativePlatformPairedBeaconService.after
        (fun query=>StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner kernel outcome).run env))).run before)) :
    result.2=before++if role=.beacon ∧ success result.1.1=true then [.owner owner] else [] := by
  simp only [after_run,simulateQ_map,StateT.run_map,support_map] at supported
  obtain ⟨reached,called,same⟩ := supported
  cases same
  exact service_after role owner kernel outcome before reached called

/-- Both literal known/hidden first-record branches preserve all prefix effects and append only their own successful owner handle. -/
theorem stage (role : Role) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : RegistrationNativePairedChoice.Choice n) (envBefore : EnvState Auxiliary) (before : List Handle)
    (result : (RustM RegistrationNativePairedBeaconService.Result × EnvState Auxiliary) × List Handle)
    (supported : result∈support ((simulateQ (handler role) (simulateQ effects
      ((RegistrationNativePlatformPairedBeaconOwner.publicBranch crypto
        (RegistrationBeaconChargedSource.primitive
          (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
        (fun query=>StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _))
        owner descriptor choice).run envBefore))).run before)) :
    result.2=before++if role=.beacon ∧ success result.1.1=true then [.owner owner] else [] := by
  cases choice <;>
    simp only [RegistrationNativePlatformPairedBeaconOwner.publicBranch,RegistrationNativePlatformPairedBeaconOwner.knownStage,
      RegistrationNativePlatformPairedBeaconOwner.publicHidden,RegistrationNativePlatformPairedBeaconOwner.hiddenStage,
      StateT.run_bind,simulateQ_bind,StateT.run_bind] at supported
  all_goals
    rw [effects_free role _ (RegistrationNativePlatformPairedBeaconRawFree.program_free crypto writer role _ envBefore)] at supported
    simp only [bind_map_left,mem_support_bind_iff] at supported
    obtain ⟨opened,_called,continued⟩ := supported
    exact after_state role owner _ opened.1 opened.2 before result continued

private def collapse : RustM RegistrationNativePairedBeaconService.Result → RustM (Option Pqxdh.Bytes)
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err _) => .ok none
  | .ok (.Ok completed) => .ok (some (TranscriptAuthParts.absSlice completed.application))

private theorem collapse_present (published : RustM RegistrationNativePairedBeaconService.Result) :
    success published=RegistrationNativeInstallBeaconComplete.present (collapse published) := by
  cases published with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {source : RegistrationNativeMldsa.Source}

private theorem settled_free (role : Role) (owner current : SelectedOwner source)
    (published : RustM RegistrationNativePairedBeaconService.Result) (envBefore : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.after
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner published).run current).run envBefore).IsQueryBoundP
      (RegistrationNativeSecretWordAtomInstallCaps.InstallEnv role) 0 := by
  cases published with
  | fail error | div =>
      simp [RegistrationNativePlatformBeaconMaterialFrontend.after,RegistrationNativePlatformBeaconMaterialFrontend.abort,
        seqRight_eq_bind,StateT.run_lift,StateT.run_map,bind_pure_comp,QueryImpl.ofLift,
        RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,isQueryBoundP_query_iff]
  | ok result => cases result with
    | Err previous =>
        simp [RegistrationNativePlatformBeaconMaterialFrontend.after,RegistrationNativePlatformBeaconMaterialFrontend.abort,
          seqRight_eq_bind,StateT.run_lift,StateT.run_map,bind_pure_comp,QueryImpl.ofLift,
          RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,isQueryBoundP_query_iff]
    | Ok completed => trivial

private theorem settled_value (owner current : SelectedOwner source)
    (published : RustM RegistrationNativePairedBeaconService.Result) (envBefore : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (supported : result∈support (simulateQ effects (((RegistrationNativePlatformBeaconMaterialFrontend.after
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner published).run current).run envBefore))) :
    result.1.1=collapse published := by
  cases published with
  | fail error | div =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,RegistrationNativePlatformBeaconMaterialFrontend.abort,
        seqRight_eq_bind,StateT.run_lift,StateT.run_map,bind_pure_comp,QueryImpl.ofLift,
        simulateQ_map,support_map] at supported
      obtain ⟨reached,_called,equal⟩ := supported
      cases equal
      rfl
  | ok result => cases result with
    | Err previous =>
        simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,RegistrationNativePlatformBeaconMaterialFrontend.abort,
          seqRight_eq_bind,StateT.run_lift,StateT.run_map,bind_pure_comp,QueryImpl.ofLift,
          simulateQ_map,support_map] at supported
        obtain ⟨reached,_called,equal⟩ := supported
        cases equal
        rfl
    | Ok completed =>
        simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,StateT.run_bind,StateT.run_modify,
          pure_bind,StateT.run_pure,simulateQ_pure,mem_support_pure_iff] at supported
        cases supported
        rfl

/-- The complete first-record material program appends exactly its captured physical owner on successful returned application bytes. -/
theorem program_handles (role : Role) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (envBefore : EnvState Auxiliary) (before : List Handle)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × List Handle)
    (supported : result∈support ((simulateQ (handler role) (simulateQ effects
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run envBefore))).run before)) :
    result.2=before++if role=.beacon ∧ RegistrationNativeInstallBeaconComplete.present result.1.1.1=true then [.owner owner.worldOwner] else [] := by
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.program,valid,ite_true,ite_false,
      StateT.run_bind,StateT.run_lift,RegistrationBeaconMaterialRead.charge,StateT.run_modify,pure_bind,
      bind_pure_comp,bind_map_left,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨published,material,settled⟩ := supported
    have first := stage role crypto writer owner.worldOwner ready.descriptor choice _ before published material
    rw [effects_free role _ (settled_free role owner current published.1.1 published.1.2),support_map] at settled
    obtain ⟨finished,actual,equal⟩ := settled
    cases equal
    have value := settled_value (n := n) (KemSK := KemSK) owner current published.1.1 published.1.2 finished actual
    rw [first,collapse_present,←value]

/-- Final phase settlement adds no installation and preserves the actual returned application's success flag. -/
theorem settled_handles (role : Role) (owner current : SelectedOwner source)
    (published : RustM RegistrationNativePairedBeaconService.Result) (envBefore : EnvState Auxiliary) (before : List Handle)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × List Handle)
    (supported : result∈support ((simulateQ (handler role) (simulateQ effects
      (((RegistrationNativePlatformBeaconMaterialFrontend.after
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner published).run current).run envBefore))).run before)) :
    result.2=before ∧ RegistrationNativeInstallBeaconComplete.present result.1.1.1=success published := by
  rw [effects_free role _ (settled_free role owner current published envBefore),support_map] at supported
  obtain ⟨finished,called,equal⟩ := supported
  cases equal
  have value := settled_value (n := n) (KemSK := KemSK) owner current published envBefore finished called
  exact ⟨rfl,(congrArg RegistrationNativeInstallBeaconComplete.present value).trans (collapse_present published).symm⟩


end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.service_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.service_after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.after_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.after_state

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.stage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.program_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.program_handles

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.settled_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles.settled_handles
