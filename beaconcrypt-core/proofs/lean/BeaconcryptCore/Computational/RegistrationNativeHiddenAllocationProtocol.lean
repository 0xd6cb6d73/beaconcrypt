-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocol

/-! Allocation is decided by the actual public Protocol controller, before any private service reply. Exactly appendOwner adds one slot and returns the previous length. Other native operations retain owner-slot count, and a successful Beacon installation requires an already existing InitSent slot. These source facts hold for arbitrary private service outputs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol
open PqxdhRecordLiftInterface (CapabilitySpec EnvEffects WorldSpec)
open PqxdhRecordLiftProtocol (Control ServiceSpec)
variable {n : Nat}

def capabilityDelta : (CapabilitySpec n).Domain → Nat
  | .appendOwner _ _ _ => 1
  | _ => 0

def effectDelta : (EnvEffects n).Domain → Nat
  | .inr capability => capabilityDelta capability
  | .inl _ => 0

def delta : (WorldSpec n).Domain → Nat
  | .inr (.inl effect) => effectDelta effect
  | _ => 0

private theorem install_server_length (keyId : U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (ref : PqxdhRecordLiftInterface.KernelRef n) (before : Control n) (result : Bool × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.installServer keyId binding ref).run before)) :
    result.2.owners.length = before.owners.length := by
  simp only [PqxdhRecordLiftProtocol.installServer, StateT.run] at supported
  repeat' split at supported
  all_goals first
    | rw [mem_support_pure_iff] at supported; cases supported; rfl
    | simp only [bind_pure_comp, support_map] at supported
      obtain ⟨stored, _reached, rfl⟩ := supported
      cases ref <;> rfl

private theorem install_beacon_length (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (ref : PqxdhRecordLiftInterface.KernelRef n) (before : Control n) (result : Bool × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.installBeacon owner shell ref).run before)) :
    result.2.owners.length = before.owners.length := by
  simp only [PqxdhRecordLiftProtocol.installBeacon, StateT.run] at supported
  split at supported
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨stored, _reached, rfl⟩ := supported
    simp only [List.length_set]
  · rw [mem_support_pure_iff] at supported; cases supported; rfl

/-- A successful actual Beacon installation targets an existing slot; no private service reply can authorize a missing owner. -/
theorem install_beacon_present (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (ref : PqxdhRecordLiftInterface.KernelRef n) (before after : Control n)
    (supported : (true, after) ∈ support ((PqxdhRecordLiftProtocol.installBeacon owner shell ref).run before)) :
    before.owners[owner]? = some (.inactive .initSent) := by
  simp only [PqxdhRecordLiftProtocol.installBeacon, StateT.run] at supported
  split at supported
  · rename_i admitted
    exact admitted.1
  · simp only [mem_support_pure_iff, Prod.mk.injEq, Bool.true_eq_false, false_and] at supported

/-- The complete actual capability surface changes owner count only for its literal append operation. -/
theorem capability_length (query : (CapabilitySpec n).Domain) (before : Control n)
    (result : (CapabilitySpec n).Range query × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.capability query).run before)) :
    result.2.owners.length = before.owners.length + capabilityDelta query := by
  cases query with
  | peerPresent keyId | ownerPresent owner =>
      simp only [PqxdhRecordLiftProtocol.capability, StateT.run, mem_support_pure_iff] at supported
      cases supported
      rfl
  | appendOwner sender identity phase =>
      simp only [PqxdhRecordLiftProtocol.capability, StateT.run, mem_support_pure_iff] at supported
      cases supported
      simp only [List.length_append, List.length_singleton, capabilityDelta]
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftProtocol.capability, StateT.run] at supported
      repeat' split at supported
      all_goals rw [mem_support_pure_iff] at supported
      all_goals cases supported
      all_goals simp only [List.length_set, capabilityDelta, Nat.add_zero]
  | installServer keyId binding ref => exact install_server_length keyId binding ref before result supported
  | installBeacon owner shell ref => exact install_beacon_length owner shell ref before result supported
  | hash bytes =>
      simp only [PqxdhRecordLiftProtocol.capability, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨digest, _reached, rfl⟩ := supported
      rfl

/-- The actual counted append executes its charge before returning precisely the old owner length and adding its inactive slot. -/
theorem append_run (sender : U64) (identity : RawCtxServerRouting.Identity) (phase : PqxdhRecordLiftInterface.InactivePhase)
    (before : Control n) :
    (PqxdhRecordLiftProtocol.effects (.inr (.appendOwner sender identity phase))).run before =
      (fun (_ : Unit) => (before.owners.length, { before with owners := before.owners ++ [.inactive phase] })) <$>
        ((ServiceSpec n).query (.charge (PqxdhRecordLiftInterface.effectKind (n := n) (.inr (.appendOwner sender identity phase)))) : OracleComp (ServiceSpec n) Unit) := by
  simp only [PqxdhRecordLiftProtocol.effects, PqxdhRecordLiftProtocol.capability,
    StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  rfl

/-- The direct native append receipt retains the allocator's exact prior index for arbitrary charge-service replies. -/
theorem append_facts (sender : U64) (identity : RawCtxServerRouting.Identity) (phase : PqxdhRecordLiftInterface.InactivePhase)
    (before : Control n) (result : Nat × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.effects (.inr (.appendOwner sender identity phase))).run before)) :
    result.1 = before.owners.length ∧ result.2.owners.length = before.owners.length + 1 := by
  rw [append_run, support_map] at supported
  obtain ⟨reply, _charged, rfl⟩ := supported
  exact ⟨rfl, by simp only [List.length_append, List.length_singleton]⟩

/-- Counted native installation retains the same public existence check after charging. -/
theorem effects_install_beacon_present (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (ref : PqxdhRecordLiftInterface.KernelRef n) (before after : Control n)
    (supported : (true, after) ∈ support
      ((PqxdhRecordLiftProtocol.effects (.inr (.installBeacon owner shell ref))).run before)) :
    before.owners[owner]? = some (.inactive .initSent) := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨charged, _charged, continued⟩ := supported
  exact install_beacon_present owner shell ref before after continued

/-- Charging and arbitrary primitive coins do not allocate owner slots. -/
theorem effects_length (query : (EnvEffects n).Domain) (before : Control n)
    (result : (EnvEffects n).Range query × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.effects query).run before)) :
    result.2.owners.length = before.owners.length + effectDelta query := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨charged, _charged, continued⟩ := supported
  cases query with
  | inl coin =>
      simp only [StateT.run_lift, bind_pure_comp, support_map] at continued
      obtain ⟨reply, _sampled, rfl⟩ := continued
      rfl
  | inr query => exact capability_length query before result continued

private theorem server_length (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (before : Control n)
    (result : RawCtxServerMixed.SourceSpec.Range query × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.serverStep decode route query).run before)) :
    result.2.owners.length = before.owners.length := by
  simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run] at supported
  repeat' split at supported
  all_goals first
    | rw [mem_support_pure_iff] at supported; cases supported; rfl
    | simp only [bind_pure_comp, support_map] at supported
      obtain ⟨current, _reached, rfl⟩ := supported
      rfl

private theorem beacon_length (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (before : Control n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.beaconStep decode owner query).run before)) :
    result.2.owners.length = before.owners.length := by
  cases selected : before.owners[owner]? with
  | none => simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, selected, mem_support_pure_iff] at supported; cases supported; rfl
  | some phase => cases phase with
    | inactive phase => cases query <;>
        simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, selected, mem_support_pure_iff] at supported <;>
        cases supported <;> rfl
    | established shell kernel =>
        simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, selected, bind_pure_comp, support_map] at supported
        obtain ⟨current, _reached, rfl⟩ := supported
        simp only [List.length_set]

/-- Every actual World query has its exact allocation delta before any private service interpretation. -/
theorem query_length (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (before : Control n)
    (result : (WorldSpec n).Range query × Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run before)) :
    result.2.owners.length = before.owners.length + delta query := by
  cases query with
  | inl created =>
      cases found : before.server <;>
        simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.initializeServer,
          StateT.run, found, mem_support_pure_iff] at supported <;> cases supported <;> rfl
  | inr query => cases query with
    | inl effect => exact effects_length effect before result supported
    | inr record => cases record with
      | inl query => cases query with
        | inl send => exact server_length decode route (.inl send) before result supported
        | inr raw => exact server_length decode route (.inr raw) before result supported
      | inr owner =>
          rcases owner with ⟨owner, query⟩
          cases query with
          | inl plaintext => exact beacon_length decode owner (.inl plaintext) before result supported
          | inr raw => exact beacon_length decode owner (.inr raw) before result supported

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.install_beacon_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.install_beacon_present
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.capability_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.capability_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.append_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.append_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.append_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.append_facts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.effects_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.effects_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.query_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.query_length

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.effects_install_beacon_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol.effects_install_beacon_present
