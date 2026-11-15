-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity
import BeaconcryptCore.Refinement.RegistrationAd
import BeaconcryptCore.Refinement.PqxdhConcreteSession

/-! Actual source initializer construction retains the exact root/input and the two role-specific chain partitions. This is a functional source fact used before identifying actual initial-KDF replies and kernels. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitializerFields
open PqxdhInitialRatchetComplementarity (serverPending beaconPending)

/-- The Server candidate starts the original role initializer at the actual token root. -/
theorem server_start (candidate : pqxdh.ServerRegistrationCandidate) (root : Std.Array U8 32#usize) :
    pqxdh.concrete.start_server_candidate_ratchet_kdf candidate root = .ok (serverPending root) := by
  change pqxdh.concrete.start_server_ratchet_kdf root = _
  exact pqxdh.concrete.start_server_ratchet_kdf_exact root

/-- The Beacon candidate starts the opposite original role initializer at the actual agreement root. -/
theorem beacon_start (candidate : pqxdh.BeaconRegistrationCandidate) (root : Std.Array U8 32#usize) :
    pqxdh.concrete.start_beacon_candidate_ratchet_kdf candidate root = .ok (beaconPending root) := by
  change pqxdh.concrete.start_beacon_ratchet_kdf root = _
  exact pqxdh.concrete.start_beacon_ratchet_kdf_exact root

/-- Actual successful Server completion retains the canonical pending role initializer and its exact request. -/
theorem server (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (capability : agreement.ServerAgreement) (application : Slice U8)
    (initial : registration.ServerInitialKdf)
    (started : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability capability application initial) :
    initial.pending = serverPending capability.root.bytes ∧
      initial.request = .ok ⟨capability.root.bytes, ratchet.INITIAL_RATCHET_INFO⟩ := by
  have same := BeaconcryptCore.Refinement.RegistrationAd.server_admission_pending
    control pin availability capability application initial started
  exact ⟨same, by simp only [registration.ServerInitialKdf.request, same, pqxdh.concrete.InitialRatchetKdfPending.impl.request]; rfl⟩

/-- Actual Beacon completion retains its root-bearing agreement, canonical opposite role pending value and exact request. -/
theorem beacon (capability : agreement.BeaconAgreement) (initial : registration.BeaconInitialKdf)
    (started : registration.begin_beacon_completion capability = .ok initial) :
    initial.agreement = capability ∧ initial.pending = beaconPending capability.root.bytes ∧
      initial.request = .ok ⟨capability.root.bytes, ratchet.INITIAL_RATCHET_INFO⟩ := by
  have actual : registration.begin_beacon_completion capability = .ok ⟨capability, beaconPending capability.root.bytes⟩ := by
    simp only [registration.begin_beacon_completion, ratchet.RatchetChain.as_bytes, bind_tc_ok, beacon_start]
  cases RustM.ok.inj (started.symm.trans actual)
  exact ⟨rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeInitializerFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializerFields.server_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializerFields.server_start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializerFields.beacon_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializerFields.beacon_start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializerFields.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializerFields.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializerFields.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializerFields.beacon
