-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallInsert

/-! Exact native post-publication controllers couple successful public results to their single same-role successful trace event; every earlier native failure has an empty successful suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallAfter
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeG2Trace (State handler)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallInsert (success effects)
open RegistrationNativeRelatedFamily (Message)
variable {n : Nat} {KemSK Encoded : Type}

private theorem failed (role : Role) (value : RustM (RegistrationNativePairedServerService.Result Encoded))
    (unsuccessful : success value = false) (before : State) (message : Message)
    (result : RustM (RegistrationNativePairedServerService.Result Encoded) × State)
    (supported : result ∈ support (pure (value, before) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1 = true then [message] else [] := by
  rw [mem_support_pure_iff] at supported
  cases supported
  simp only [unsuccessful, Bool.false_eq_true, and_false, ite_false, List.append_nil]

/-- All actual ordinary Server post-publication failures and successful insertion Bool replies have their exact successful descriptor bill. -/
theorem server (role : Role) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (before : State) (message : Message) (active : before.current = some message)
    (result : RustM (RegistrationNativePairedServerService.Result Encoded) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effects (n := n) (KemSK := KemSK))
      (RegistrationNativePairedServerService.knownAfter control published))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1 = true then [message] else [] := by
  cases published with
  | fail error => exact failed role (.fail error) rfl before message result supported
  | div => exact failed role .div rfl before message result supported
  | ok outcome => cases outcome with
    | Err previous => exact failed role (.ok (.Err previous)) rfl before message result supported
    | Ok published =>
        change result ∈ support ((simulateQ handler (simulateQ effects
          (RegistrationNativePairedServerService.knownInstall control published))).run before) at supported
        cases prepared : peer.begin_peer_insert control published with
        | fail error =>
            simp only [RegistrationNativePairedServerService.knownInstall, prepared] at supported
            exact failed role (.fail error) rfl before message result supported
        | div =>
            simp only [RegistrationNativePairedServerService.knownInstall, prepared] at supported
            exact failed role .div rfl before message result supported
        | ok outcome => cases outcome with
          | Err previous =>
              simp only [RegistrationNativePairedServerService.knownInstall, prepared] at supported
              exact failed role (.ok (.Err previous)) rfl before message result supported
          | Ok pending => exact RegistrationNativeInstallInsert.server role control published pending prepared before message active result supported

/-- The actual hidden Server post-publication path has exactly the same successful bill, retaining its selected slot. -/
theorem server_hidden (role : Role) (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (before : State) (message : Message) (active : before.current = some message)
    (result : RustM (RegistrationNativePairedServerService.Result Encoded) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effects (n := n) (KemSK := KemSK))
      (RegistrationHiddenInstall.after control slot published))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1 = true then [message] else [] := by
  cases published with
  | fail error => exact failed role (.fail error) rfl before message result supported
  | div => exact failed role .div rfl before message result supported
  | ok outcome => cases outcome with
    | Err previous => exact failed role (.ok (.Err previous)) rfl before message result supported
    | Ok published =>
        change result ∈ support ((simulateQ handler (simulateQ effects
          (RegistrationHiddenInstall.install control slot published))).run before) at supported
        cases prepared : peer.begin_peer_insert control published with
        | fail error =>
            simp only [RegistrationHiddenInstall.install, prepared] at supported
            exact failed role (.fail error) rfl before message result supported
        | div =>
            simp only [RegistrationHiddenInstall.install, prepared] at supported
            exact failed role .div rfl before message result supported
        | ok outcome => cases outcome with
          | Err previous =>
              simp only [RegistrationHiddenInstall.install, prepared] at supported
              exact failed role (.ok (.Err previous)) rfl before message result supported
          | Ok pending => exact RegistrationNativeInstallInsert.server_hidden role control slot published pending prepared before message active result supported

/-- All actual Beacon opening/admission failures retain an empty successful suffix; final native admission has the original Bool bill. -/
theorem beacon (role : Role) (owner : Nat) (sender : U64)
    (kernel : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (opened : RustM RegistrationBeaconRecordExecutor.Result)
    (before : State) (message : Message) (active : before.current = some message)
    (result : RustM RegistrationNativePairedBeaconService.Result × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effects (n := n) (KemSK := KemSK))
      (RegistrationNativePairedBeaconService.after owner sender kernel opened))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .beacon ∧ success result.1 = true then [message] else [] := by
  cases opened with
  | fail error =>
      change result ∈ support (pure (.fail error, before) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) at supported
      rw [mem_support_pure_iff] at supported
      cases supported
      simp only [success, Bool.false_eq_true, and_false, ite_false, List.append_nil]
  | div =>
      change result ∈ support (pure (.div, before) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) at supported
      rw [mem_support_pure_iff] at supported
      cases supported
      simp only [success, Bool.false_eq_true, and_false, ite_false, List.append_nil]
  | ok outcome => cases outcome with
    | Err aborted =>
        change result ∈ support (pure (.ok (.Err aborted), before) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) at supported
        rw [mem_support_pure_iff] at supported
        cases supported
        simp only [success, Bool.false_eq_true, and_false, ite_false, List.append_nil]
    | Ok completed => exact RegistrationNativeInstallInsert.beacon role owner sender kernel completed before message active result supported
end BeaconcryptCore.Computational.RegistrationNativeInstallAfter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallAfter.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallAfter.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallAfter.server_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallAfter.server_hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallAfter.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallAfter.beacon
