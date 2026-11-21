-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend

/-! Each actual paired material continuation can attempt installation only once, in its own role. The record, hash, signing and encoding programs remain arbitrary typed publication/raw programs in this footprint proof, so none of their native optional failure paths are omitted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativePairedServerService (Common)
variable {n : Nat} {Value Encoded : Type}

def InstallEnv (role : Role) : (EnvEffects n).Domain → Prop
  | .inr (.installServer _ _ _) => role = .server
  | .inr (.installBeacon _ _ _) => role = .beacon
  | _ => False
instance (role : Role) : DecidablePred (InstallEnv (n := n) role) := fun query => by
  rcases query with coin | capability
  · exact isFalse id
  · cases capability <;> dsimp only [InstallEnv] <;> infer_instance

def Install (role : Role) : (Common n).Domain → Prop
  | .inl _ => False
  | .inr query => InstallEnv role query
instance (role : Role) : DecidablePred (Install (n := n) role) := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr query => exact inferInstanceAs (Decidable (InstallEnv role query))

private theorem publication_free (role : Role) (work : OracleComp RegistrationBoundPublication.Spec Value) :
    (simulateQ RegistrationHiddenInstall.publicationLift work).IsQueryBoundP (Install (n := n) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationHiddenInstall.publicationLift, Install, isQueryBoundP_query_iff]

private theorem raw_free (role : Role) (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    (simulateQ RegistrationNativePairedBeaconService.rawLift work).IsQueryBoundP (Install (n := n) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativePairedBeaconService.rawLift, Install, isQueryBoundP_query_iff]

private theorem effects_bound (role : Role) (work : OracleComp (EnvEffects n) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (InstallEnv role) cap) :
    (simulateQ RegistrationHiddenInstall.effectLift work).IsQueryBoundP (Install role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  by_cases charged : InstallEnv role query <;>
    simp [RegistrationHiddenInstall.effectLift, Install, charged, isQueryBoundP_query_iff]

private theorem server_known (role : Role) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    (RegistrationNativePairedServerService.knownInstall (n := n) control published).IsQueryBoundP (InstallEnv role)
      (if role = .server then 1 else 0) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
    | Ok pending =>
        cases requested : pending.request with
        | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
        | ok keyId =>
            cases divided : pending.into_parts with
            | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
            | ok parts =>
                simp only [RegistrationNativePairedServerService.knownInstall, prepared]
                change OracleComp.IsQueryBoundP (((EnvEffects n).query (.inr (.installServer keyId (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.known parts.1.ratchet))) : OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) (InstallEnv role) (if role = .server then 1 else 0)
                cases role <;> simp [InstallEnv]

private theorem server_hidden (role : Role) (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : registration.PublishedServerResponse Encoded) :
    (RegistrationHiddenInstall.install control slot published).IsQueryBoundP (InstallEnv role)
      (if role = .server then 1 else 0) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
  | ok result => cases result with
    | Err previous => simp only [RegistrationHiddenInstall.install, prepared]; trivial
    | Ok pending =>
        cases requested : pending.request with
        | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
        | ok keyId =>
            cases divided : pending.into_parts with
            | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
            | ok parts =>
                simp only [RegistrationHiddenInstall.install, prepared]
                change OracleComp.IsQueryBoundP (((EnvEffects n).query (.inr (.installServer keyId (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.hidden slot))) : OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) (InstallEnv role) (if role = .server then 1 else 0)
                cases role <;> simp [InstallEnv]

private theorem server_known_after (role : Role) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    (RegistrationNativePairedServerService.knownAfter (n := n) control published).IsQueryBoundP (InstallEnv role)
      (if role = .server then 1 else 0) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_known role control published

private theorem server_hidden_after (role : Role) (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    (RegistrationHiddenInstall.after control slot published).IsQueryBoundP (InstallEnv role)
      (if role = .server then 1 else 0) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_hidden role control slot published

private theorem bind_zero {Index X Y : Type} {spec : OracleSpec Index}
    {predicate : spec.Domain → Prop} [DecidablePred predicate] {cap : Nat}
    {work : OracleComp spec X} {next : X → OracleComp spec Y}
    (first : work.IsQueryBoundP predicate 0)
    (later : ∀ value ∈ support work, (next value).IsQueryBoundP predicate cap) :
    (work >>= next).IsQueryBoundP predicate cap := by
  simpa only [Nat.zero_add] using isQueryBoundP_bind (n := 0) (m := cap) first later

/-- Actual Server public material attempts at most one Server installation and no Beacon installation. -/
theorem server_branch (role : Role) (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) :
    (RegistrationNativePairedServerService.publicBranch encode control initial choice).IsQueryBoundP (Install role)
      (if role = .server then 1 else 0) := by
  cases choice with
  | known output =>
      simp only [RegistrationNativePairedServerService.publicBranch, RegistrationNativePairedServerService.knownStage]
      apply bind_zero (publication_free role _)
      intro published _
      exact effects_bound role _ _ (server_known_after role control published)
  | hidden reference =>
      simp only [RegistrationNativePairedServerService.publicBranch, RegistrationNativePairedServerService.hiddenStage]
      apply bind_zero (publication_free role _)
      intro published _
      exact effects_bound role _ _ (server_hidden_after role control reference.slot published)

private theorem beacon_after (role : Role) (owner : Nat) (sender : U64)
    (selectKernel : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) :
    (RegistrationNativePairedBeaconService.after owner sender selectKernel result).IsQueryBoundP (InstallEnv role)
      (if role = .beacon then 1 else 0) := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err aborted => trivial
    | Ok completed => cases role <;>
        simp [RegistrationNativePairedBeaconService.after, InstallEnv]

/-- Actual Beacon public material attempts at most one Beacon installation and no Server installation. -/
theorem beacon_branch (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : RegistrationNativePairedChoice.Choice n) :
    (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice).IsQueryBoundP (Install role)
      (if role = .beacon then 1 else 0) := by
  cases choice with
  | known output =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.knownStage]
      apply bind_zero (raw_free role _)
      intro result _
      exact effects_bound role _ _ (beacon_after role owner sender _ result)
  | hidden reference =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.hiddenStage,
        RegistrationNativePairedBeaconService.privateHiddenStage]
      apply bind_zero (raw_free role _)
      intro result _
      exact effects_bound role _ _ (beacon_after role owner sender _ result)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps.server_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps.server_branch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps.beacon_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps.beacon_branch
