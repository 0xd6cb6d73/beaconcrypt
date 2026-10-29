-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots

/-! Successful original Protocol installation records the exact hidden slot at the actual peer or physical owner handle. Private allocation returns only unit and cannot alter this control-side origin. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordHiddenInstall
open PqxdhRecordLiftInterface (Slot PeerBinding BeaconShell)
open PqxdhRecordLiftProtocol (Control)
variable {n : Nat}

/-- A successful actual hidden Server installation writes that same slot at its assigned peer handle. -/
theorem server (keyId : U64) (binding : PeerBinding) (slot : Slot n) (before after : Control n)
    (supported : (true, after) ∈ support ((PqxdhRecordLiftProtocol.installServer keyId binding (.hidden slot)).run before)) :
    PqxdhRecordLiftIdeal.handleSlot after (.peer keyId) = some slot := by
  cases existing : before.server with
  | none =>
      simp only [PqxdhRecordLiftProtocol.installServer, StateT.run, existing, mem_support_pure_iff,
        Prod.mk.injEq, Bool.true_eq_false, false_and] at supported
  | some server =>
      simp only [PqxdhRecordLiftProtocol.installServer, StateT.run, existing] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨stored, reached, returned⟩ := supported
        have origin := (PqxdhRecordLiftProtocolHistory.resolve_facts .server (.hidden slot) stored reached).2
        simp only [Prod.mk.injEq, true_and] at returned
        subst after
        simpa only [PqxdhRecordLiftIdeal.handleSlot, PqxdhRecordLiftIdeal.peerSlot,
          Option.bind_some, Function.update_self, PqxdhRecordLiftOrigins.origin] using origin
      · simp only [mem_support_pure_iff, Prod.mk.injEq, Bool.true_eq_false, false_and] at supported

/-- A successful actual hidden Beacon installation writes that same slot at its existing physical owner handle. -/
theorem beacon (owner : Nat) (shell : BeaconShell) (slot : Slot n) (before after : Control n)
    (supported : (true, after) ∈ support ((PqxdhRecordLiftProtocol.installBeacon owner shell (.hidden slot)).run before)) :
    PqxdhRecordLiftIdeal.handleSlot after (.owner owner) = some slot := by
  simp only [PqxdhRecordLiftProtocol.installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨stored, reached, returned⟩ := supported
    have origin := (PqxdhRecordLiftProtocolHistory.resolve_facts .beacon (.hidden slot) stored reached).2
    have below : owner < before.owners.length := (List.getElem?_eq_some_iff.mp admitted.1).1
    simp only [Prod.mk.injEq, true_and] at returned
    subst after
    simpa only [PqxdhRecordLiftIdeal.handleSlot, PqxdhRecordLiftIdeal.ownerSlot,
      PqxdhRecordLiftProtocol.markUsed, List.getElem?_set_self below, Option.bind_some,
      PqxdhRecordLiftWorldCompiler.Phase.origin, PqxdhRecordLiftOrigins.origin] using origin
  · simp only [mem_support_pure_iff, Prod.mk.injEq, Bool.true_eq_false, false_and] at supported

end BeaconcryptCore.Computational.RegistrationNativeRecordHiddenInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenInstall.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenInstall.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenInstall.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenInstall.beacon
