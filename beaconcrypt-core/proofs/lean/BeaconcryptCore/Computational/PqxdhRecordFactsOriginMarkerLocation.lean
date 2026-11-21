-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch

/-! Successful physical receives already have an installed source kernel. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation
open PqxdhRecordLiftIdeal (handleSlot)
open PqxdhRecordLiftFlat (KnownAt)
open PqxdhRecordFactsOriginHandles
open PqxdhRecordLiftWorldCompiler (StoredKernel)
open PqxdhDeploymentInterface (Handle)
variable {n : Nat}

/-- Kernel lookup classifies the current physical handle without any cryptographic execution premise. -/
theorem stored_location (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle)
    (kernel : StoredKernel n) (stored : handleKernel control handle = some kernel) :
    KnownAt control handle ∨ ∃ slot, handleSlot control handle = some slot := by
  cases kernel with
  | known kernel => exact Or.inl (PqxdhRecordFactsOriginPublished.known_of_handleKernel control handle kernel stored)
  | hidden slot kernel => exact Or.inr ⟨slot, handleKernel_slot control handle slot kernel stored⟩

/-- Successful source Server delivery uses a kernel installed before that receive, for arbitrary typed service replies. -/
theorem server_location (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (raw : Pqxdh.Bytes) (keyId : Std.U64)
    (routed : route raw = some keyId)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.serverStep read route (.inr raw) control))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    KnownAt control (.peer keyId) ∨ ∃ slot, handleSlot control (.peer keyId) = some slot := by
  cases existing : control.server with
  | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at returned
  | some server =>
      cases found : server.peers keyId with
      | none =>
          simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, support_pure, Set.mem_singleton_iff] at supported
          simp only [supported, reduceCtorEq] at returned
      | some peer =>
          apply stored_location control (.peer keyId) peer.kernel
          simp only [handleKernel, existing, Option.bind_some, found, Option.map_some]

/-- Successful source Beacon delivery uses an established kernel present before that receive, for arbitrary typed service replies. -/
theorem beacon_location (read : RawCtxReceive.FrameDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (index : Nat) (raw : Pqxdh.Bytes)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.beaconStep read index (.inr raw) control))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    KnownAt control (.owner index) ∨ ∃ slot, handleSlot control (.owner index) = some slot := by
  rcases found : control.owners[index]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, PqxdhDeploymentNative.absent, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · apply stored_location control (.owner index) kernel
    simp only [handleKernel, found, Option.bind_some]

/-- An installed receive handle remains either caller-known or hidden under the actual forward control transition. -/
theorem location_mono (before after : PqxdhRecordLiftProtocol.Control n)
    (progress : PqxdhRecordLiftProtocolHistory.Step before after)
    (known : ∀ handle, KnownAt before handle → KnownAt after handle)
    (handle : Handle) (located : KnownAt before handle ∨ ∃ slot, handleSlot before handle = some slot) :
    KnownAt after handle ∨ ∃ slot, handleSlot after handle = some slot := by
  rcases located with prior | ⟨slot, present⟩
  · exact Or.inl (known handle prior)
  · exact Or.inr ⟨slot, handleSlot_step before after progress handle slot present⟩

/-- A final hidden slot can be pulled back only when the actual earlier receive has proved its handle was already installed; known-to-hidden conversion is excluded separately. -/
theorem slot_before (before after : PqxdhRecordLiftProtocol.Control n)
    (progress : PqxdhRecordLiftProtocolHistory.Step before after)
    (known : ∀ handle, KnownAt before handle → KnownAt after handle)
    (handle : Handle) (located : KnownAt before handle ∨ ∃ slot, handleSlot before handle = some slot)
    (slot : PqxdhRecordLiftInterface.Slot n) (present : handleSlot after handle = some slot) :
    handleSlot before handle = some slot := by
  rcases located with prior | ⟨old, found⟩
  · simp only [PqxdhRecordFactsOriginAccepted.known_no_slot after handle (known handle prior), reduceCtorEq] at present
  · have equal := (handleSlot_step before after progress handle old found).symm.trans present
    simpa only [Option.some.inj equal] using found

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.stored_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.stored_location

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.server_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.server_location

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.beacon_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.beacon_location

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.location_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.location_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.slot_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation.slot_before
