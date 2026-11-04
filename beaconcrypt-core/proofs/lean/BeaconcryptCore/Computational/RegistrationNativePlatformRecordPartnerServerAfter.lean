-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles
import BeaconcryptCore.Computational.RegistrationNativeInstallAfter
/-! The actual successful Server insertion handle is the key identifier of the same returned PublishedPeer, including every earlier publication and insertion failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerAfter
open PqxdhDeploymentInterface (Handle)
open RegistrationNativePlatformRecordPartnerSnapshotHandles (update)
open RegistrationNativePairedCompile (effects)
variable {n : Nat} {KemSK Encoded : Type}
local notation "serverHandler" => RegistrationNativePlatformRecordPartnerSnapshotHandles.handler (n := n) (KemSK := KemSK) PqxdhRecordLiftInterface.Role.server

def outputHandles : RustM (RegistrationHiddenInstall.Result Encoded) → List Handle
  | .ok (.Ok published)=>[.peer published.key_id]
  | _=>[]
private theorem failed (value : RustM (RegistrationHiddenInstall.Result Encoded)) (empty : outputHandles value=[])
    (before : List Handle) (result : RustM (RegistrationHiddenInstall.Result Encoded) × List Handle)
    (supported : result∈support (pure (value,before) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _)) :
    result.2=before++outputHandles result.1 := by
  rw [mem_support_pure_iff] at supported
  cases supported
  rw [empty,List.append_nil]

/-- Ordinary insertion retains exactly the handle of its same final native published result. -/
theorem known (control : pqxdh.ServerState) (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (before : List Handle) (result : RustM (RegistrationHiddenInstall.Result Encoded) × List Handle)
    (supported : result∈support ((simulateQ serverHandler (simulateQ effects
      (RegistrationNativePairedServerService.knownAfter control published))).run before)) :
    result.2=before++outputHandles result.1 := by
  cases published with
  | fail error=>exact failed (.fail error) rfl before result supported
  | div=>exact failed .div rfl before result supported
  | ok outcome=>cases outcome with
    | Err previous=>exact failed (.ok (.Err previous)) rfl before result supported
    | Ok published=>
      change result∈support ((simulateQ serverHandler (simulateQ effects
        (RegistrationNativePairedServerService.knownInstall control published))).run before) at supported
      cases prepared : peer.begin_peer_insert control published with
      | fail error=>
        simp only [RegistrationNativePairedServerService.knownInstall,prepared] at supported
        exact failed (.fail error) rfl before result supported
      | div=>
        simp only [RegistrationNativePairedServerService.knownInstall,prepared] at supported
        exact failed .div rfl before result supported
      | ok outcome=>cases outcome with
        | Err previous=>
          simp only [RegistrationNativePairedServerService.knownInstall,prepared] at supported
          exact failed (.ok (.Err previous)) rfl before result supported
        | Ok pending=>
          rw [RegistrationNativePairedServerService.knownInstall_native control published pending prepared] at supported
          simp only [simulateQ_bind,simulateQ_spec_query,effects] at supported
          rw [StateT.run_bind] at supported
          simp only [RegistrationNativePlatformRecordPartnerSnapshotHandles.handler,StateT.run,bind_map_left,mem_support_bind_iff] at supported
          obtain ⟨inserted,_called,continued⟩ := supported
          simp only [simulateQ_pure] at continued
          cases continued
          cases inserted <;> simp [update,outputHandles,peer.PublicationFinish.finish]

/-- Hidden insertion retains the same public key identifier without exposing its hidden slot. -/
theorem hidden (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (before : List Handle) (result : RustM (RegistrationHiddenInstall.Result Encoded) × List Handle)
    (supported : result∈support ((simulateQ serverHandler (simulateQ effects
      (RegistrationHiddenInstall.after control slot published))).run before)) :
    result.2=before++outputHandles result.1 := by
  cases published with
  | fail error=>exact failed (.fail error) rfl before result supported
  | div=>exact failed .div rfl before result supported
  | ok outcome=>cases outcome with
    | Err previous=>exact failed (.ok (.Err previous)) rfl before result supported
    | Ok published=>
      change result∈support ((simulateQ serverHandler (simulateQ effects
        (RegistrationHiddenInstall.install control slot published))).run before) at supported
      cases prepared : peer.begin_peer_insert control published with
      | fail error=>
        simp only [RegistrationHiddenInstall.install,prepared] at supported
        exact failed (.fail error) rfl before result supported
      | div=>
        simp only [RegistrationHiddenInstall.install,prepared] at supported
        exact failed .div rfl before result supported
      | ok outcome=>cases outcome with
        | Err previous=>
          simp only [RegistrationHiddenInstall.install,prepared] at supported
          exact failed (.ok (.Err previous)) rfl before result supported
        | Ok pending=>
          rw [RegistrationHiddenInstall.install_native control slot published pending prepared] at supported
          change result∈support ((simulateQ serverHandler (simulateQ effects (do
            let inserted ← ((PqxdhRecordLiftInterface.EnvEffects n).query (.inr (.installServer pending.peer.binding.assigned_key_id
              (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding) (.hidden slot))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Bool)
            pure ((⟨pending.previous,pending.next,pending.peer.binding.assigned_key_id,pending.encoded⟩ : peer.PublicationFinish Encoded).finish inserted)))).run before) at supported
          simp only [simulateQ_bind,simulateQ_spec_query,effects] at supported
          rw [StateT.run_bind] at supported
          simp only [RegistrationNativePlatformRecordPartnerSnapshotHandles.handler,StateT.run,bind_map_left,mem_support_bind_iff] at supported
          obtain ⟨inserted,_called,continued⟩ := supported
          simp only [simulateQ_pure] at continued
          cases continued
          cases inserted <;> simp [update,outputHandles,peer.PublicationFinish.finish]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerAfter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerAfter.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerAfter.known

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerAfter.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerAfter.hidden
