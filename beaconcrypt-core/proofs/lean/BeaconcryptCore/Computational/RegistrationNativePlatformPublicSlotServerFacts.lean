-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts
/-! Each literal known/hidden Server insertion uses exactly the constructor kind and slot returned by its own preceding material demand. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformPublicSlotKind (Effect)
variable {n : Nat} {Encoded : Type}
private theorem server_known (output : PqxdhServerAuthKeySchedule.Output) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownInstall (n := n) control published) (Effect .server (.known output)) := by
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
                    OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) (Effect .server (.known output))
                exact ⟨⟨rfl, rfl⟩, fun _ => trivial⟩

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
                exact ⟨⟨rfl, rfl⟩, fun _ => trivial⟩

theorem server_known_allowed (output : PqxdhServerAuthKeySchedule.Output) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownAfter (n := n) control published) (Effect .server (.known output)) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_known output control published

theorem server_hidden_allowed (reference : RegistrationNativePairedDemand.Reference n) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationHiddenInstall.after control reference.slot published) (Effect .server (.hidden reference)) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_hidden reference control published

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts.server_known_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts.server_known_allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts.server_hidden_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts.server_hidden_allowed
