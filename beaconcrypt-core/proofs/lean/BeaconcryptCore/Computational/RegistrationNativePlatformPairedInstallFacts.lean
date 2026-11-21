-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps
import BeaconcryptCore.Computational.RegistrationNativePairedProvenance
/-! Literal peer-install continuations use at most one role-specific request and the kernel reference passed by their actual known/hidden branch. These source facts retain all insertion-counter, failure and assigned-ID outcomes and assume no desired trace or security conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePairedProvenance (Effect Kernel)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
variable {n : Nat} {Encoded : Type}
private theorem server_known (choice : Choice n) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownInstall (n := n) control published) (Effect .server choice) := by
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
                change AllQueriesSatisfy (((EnvEffects n).query (.inr (.installServer keyId
                  (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.known parts.1.ratchet))) :
                    OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) (Effect .server choice)
                exact ⟨⟨rfl, trivial⟩, fun _ => trivial⟩

private theorem server_hidden (reference : RegistrationNativePairedDemand.Reference n) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationHiddenInstall.install control reference.slot published) (Effect .server (.hidden reference)) := by
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
                change AllQueriesSatisfy (((EnvEffects n).query (.inr (.installServer keyId
                  (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.hidden reference.slot))) :
                    OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) (Effect .server (.hidden reference))
                exact ⟨⟨rfl, reference, rfl, rfl⟩, fun _ => trivial⟩

theorem server_known_allowed (choice : Choice n) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownAfter (n := n) control published) (Effect .server choice) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_known choice control published

theorem server_hidden_allowed (reference : RegistrationNativePairedDemand.Reference n) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationHiddenInstall.after control reference.slot published) (Effect .server (.hidden reference)) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_hidden reference control published

private theorem known_count (role : Role) (control : pqxdh.ServerState)
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

private theorem hidden_count (role : Role) (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
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

theorem server_known_bound (role : Role) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    (RegistrationNativePairedServerService.knownAfter (n := n) control published).IsQueryBoundP (InstallEnv role)
      (if role = .server then 1 else 0) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact known_count role control published

theorem server_hidden_bound (role : Role) (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    (RegistrationHiddenInstall.after control slot published).IsQueryBoundP (InstallEnv role)
      (if role = .server then 1 else 0) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact hidden_count role control slot published


theorem beacon_allowed (owner : Nat) (choice : Choice n)
    (kernel : beaconcrypt_core.registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (compatible : ∀ completed, Kernel choice (kernel completed))
    (result : RustM RegistrationBeaconRecordExecutor.Result) :
    (RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel result).AllQueriesSatisfy
      (Effect .beacon choice) := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok completed =>
      simp only [RegistrationNativePlatformPairedBeaconService.after, QueryImpl.ofLift]
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨⟨rfl, compatible completed⟩, fun _ => by trivial⟩

theorem beacon_bound (role : Role) (owner : Nat)
    (kernel : beaconcrypt_core.registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) :
    (RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel result).IsQueryBoundP
      (InstallEnv role) (if role = .beacon then 1 else 0) := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok completed =>
      cases role <;> simp [RegistrationNativePlatformPairedBeaconService.after, QueryImpl.ofLift,
        InstallEnv]
end BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_known_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_known_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_hidden_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_hidden_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_known_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_known_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_hidden_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.server_hidden_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.beacon_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.beacon_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts.beacon_bound
