-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconCore
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete
/-! The real Beacon first-record material program has an exact successful descriptor suffix. Initial and conditional ratchet charges, raw failures and terminal owner updates remain on the original tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconMaterial
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeSecretWordInstallInsert (success)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativePlatformSecretWordAtomEffects (env)
open RegistrationNativePlatformSecretWordInstallBeaconCore (neutral stage_messages)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
variable {n : Nat} {KemSK Auxiliary : Type} {source : RegistrationNativeMldsa.Source}

private def collapse : RustM RegistrationNativePairedBeaconService.Result → RustM (Option Pqxdh.Bytes)
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err _) => .ok none
  | .ok (.Ok completed) => .ok (some (TranscriptAuthParts.absSlice completed.application))

private theorem collapse_present (published : RustM RegistrationNativePairedBeaconService.Result) :
    success published = RegistrationNativeInstallBeaconComplete.present (collapse published) := by
  cases published with
  | fail error | div => rfl
  | ok outcome => cases outcome <;> rfl

private theorem settled_free (role : Role) (owner current : SelectedOwner source)
    (published : RustM RegistrationNativePairedBeaconService.Result) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.after
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner published).run current).run before).IsQueryBoundP
      (InstallEnv role) 0 := by
  cases published with
  | fail error | div =>
    simp [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift,
      InstallEnv, isQueryBoundP_query_iff]
  | ok outcome => cases outcome with
    | Err previous =>
      simp [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
        seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift,
        InstallEnv, isQueryBoundP_query_iff]
    | Ok completed => trivial

private theorem settled_value (owner current : SelectedOwner source)
    (published : RustM RegistrationNativePairedBeaconService.Result) (before : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (supported : result ∈ support (simulateQ (env (KemSK := KemSK)) (((RegistrationNativePlatformBeaconMaterialFrontend.after
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner published).run current).run before))) :
    result.1.1 = collapse published := by
  cases published with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift,
      simulateQ_map, support_map] at supported
    obtain ⟨reached, _called, equal⟩ := supported
    cases equal
    rfl
  | ok outcome => cases outcome with
    | Err previous =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
        seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift,
        simulateQ_map, support_map] at supported
      obtain ⟨reached, _called, equal⟩ := supported
      cases equal
      rfl
    | Ok completed =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, StateT.run_bind,
        StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at supported
      cases supported
      rfl

/-- Every literal chosen material execution has exactly the successful suffix of its returned application result. -/
theorem program_messages (role : Role) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (envBefore : EnvState Auxiliary) (before : State) (message : Message) (active : before.current = some message)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (env (KemSK := KemSK))
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run envBefore))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .beacon ∧ RegistrationNativeInstallBeaconComplete.present result.1.1.1 = true then [message] else [] := by
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.program, valid, ite_true, ite_false,
      StateT.run_bind, StateT.run_lift, RegistrationBeaconMaterialRead.charge,
      StateT.run_modify, pure_bind, bind_pure_comp, bind_map_left, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at supported
    obtain ⟨published, material, settled⟩ := supported
    have first := stage_messages role crypto writer owner.worldOwner ready.descriptor choice _ before message active published material
    rw [neutral _ (fun role => settled_free role owner current published.1.1 published.1.2), support_map] at settled
    obtain ⟨finished, actual, equal⟩ := settled
    cases equal
    have value := settled_value (n := n) (KemSK := KemSK) owner current published.1.1 published.1.2 finished actual
    rw [first, collapse_present, ← value]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconMaterial.program_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconMaterial.program_messages
