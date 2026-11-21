-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTrace

/-! Successful native insertion finishes record exactly one copy of their own current demanded descriptor; failures record none. This finite receipt follows the original insertion Bool reply and retains the full chronological state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeSecretWordFrontendTrace (State handler begin finish)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeSecretWordMessage (Message)
variable {n : Nat} {KemSK Encoded Error Result : Type}

def success : RustM (core.result.Result Result Error) → Bool
  | .ok (.Ok _) => true
  | _ => false

def effects : QueryImpl (EnvEffects n) (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) :=
  fun query => (RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr query)))))

/-- The actual ordinary native Server insertion records its own demand exactly when its original API result succeeds. -/
theorem server (role : Role) (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded)
    (pending : peer.PeerInsert Encoded) (prepared : peer.begin_peer_insert control published = .ok (.Ok pending))
    (before : State) (message : Message) (active : before.current = some message)
    (result : RustM (RegistrationNativePairedServerService.Result Encoded) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effects (n := n) (KemSK := KemSK))
      (RegistrationNativePairedServerService.knownInstall control published))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1 = true then [message] else [] := by
  rw [RegistrationNativePairedServerService.knownInstall_native control published pending prepared] at supported
  simp only [simulateQ_bind, simulateQ_spec_query, effects] at supported
  rw [StateT.run_bind] at supported
  simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨inserted, _possible, continued⟩ := supported
  simp only [simulateQ_pure, ] at continued
  cases continued
  cases role <;> cases inserted <;>
    simp [peer.PublicationFinish.finish, success, begin, finish,
      RegistrationNativeSecretWordFrontendTrace.attempt, RegistrationNativeSecretWordFrontendTrace.installed,
      active, messages, List.filterMap_append]
/-- Hidden native Server insertion has the same exact successful descriptor bill at its unchanged private slot. -/
theorem server_hidden (role : Role) (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : registration.PublishedServerResponse Encoded)
    (pending : peer.PeerInsert Encoded) (prepared : peer.begin_peer_insert control published = .ok (.Ok pending))
    (before : State) (message : Message) (active : before.current = some message)
    (result : RustM (RegistrationNativePairedServerService.Result Encoded) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effects (n := n) (KemSK := KemSK))
      (RegistrationHiddenInstall.install control slot published))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1 = true then [message] else [] := by
  rw [RegistrationHiddenInstall.install_native control slot published pending prepared] at supported
  change result ∈ support ((simulateQ handler (simulateQ effects (do
    let inserted ← ((EnvEffects n).query (.inr (.installServer pending.peer.binding.assigned_key_id
      (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding) (.hidden slot))) : OracleComp (EnvEffects n) Bool)
    pure ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ : peer.PublicationFinish Encoded).finish inserted)))).run before) at supported
  simp only [simulateQ_bind, simulateQ_spec_query, effects] at supported
  rw [StateT.run_bind] at supported
  simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨inserted, _possible, continued⟩ := supported
  simp only [simulateQ_pure, ] at continued
  cases continued
  cases role <;> cases inserted <;>
    simp [peer.PublicationFinish.finish, success, begin, finish,
      RegistrationNativeSecretWordFrontendTrace.attempt, RegistrationNativeSecretWordFrontendTrace.installed,
      active, messages, List.filterMap_append]

/-- Both actual Beacon kernel branches have exactly the successful bill selected by their native installation Bool. -/
theorem beacon (role : Role) (owner : Nat) (sender : U64)
    (kernel : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (completed : registration.CompletedBeacon) (before : State) (message : Message) (active : before.current = some message)
    (result : RustM RegistrationNativePairedBeaconService.Result × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (effects (n := n) (KemSK := KemSK))
      (RegistrationNativePairedBeaconService.after owner sender kernel (.ok (.Ok completed))))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .beacon ∧ success result.1 = true then [message] else [] := by
  simp only [RegistrationNativePairedBeaconService.after, simulateQ_bind, simulateQ_spec_query, effects] at supported
  rw [StateT.run_bind] at supported
  simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨installed, _possible, continued⟩ := supported
  simp only [simulateQ_pure, ] at continued
  cases continued
  cases role <;> cases installed <;>
    simp [success, begin, finish, RegistrationNativeSecretWordFrontendTrace.attempt,
      RegistrationNativeSecretWordFrontendTrace.installed, active, messages, List.filterMap_append]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert.server_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert.server_hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallInsert.beacon
