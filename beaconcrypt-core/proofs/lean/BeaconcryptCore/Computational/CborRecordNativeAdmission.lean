-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldSimulation
import BeaconcryptCore.Computational.CborProductionBoundary

/-! The cursor filter tests the exact complete-frame admission predicate of the actual native CBOR boundary. The source sender and selected current sequence remain distinct from the assigned peer handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRecordNativeAdmission
variable {n : Nat} {KemSK : Type}

/-- This native projection discards no established sender or sequence metadata. -/
def nativeShell (state : PqxdhDeploymentNative.State KemSK) : CborRecordWorldClient.Shell :=
  ⟨some ⟨state.native.shared.2.server.identityKeyId, fun keyId =>
      (state.native.shared.2.server.server.peers keyId).map fun peer => peer.kernel.refined.control.send_sequence.val⟩,
    fun owner => (state.native.owners[owner]?).bind fun entry => match entry.beacon.phase with
      | .established _ _ kernel => some ⟨entry.beacon.identityKeyId, kernel.refined.control.send_sequence.val⟩
      | _ => none⟩

/-- Server send refusal uses the native current peer sequence and Server sender before every callback. -/
theorem server_admission (state : PqxdhDeploymentNative.State KemSK) (keyId : Std.U64) (plaintext : Pqxdh.Bytes) :
    CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext, keyId))))) (nativeShell state) =
      if CborProductionBoundary.allowed (.inr (.serverSend keyId plaintext)) state then none else some none := by
  cases found : state.native.shared.2.server.server.peers keyId <;>
    simp only [CborRecordWorldClient.refusal, nativeShell, CborProductionBoundary.allowed, found,
      Option.map_none, Option.map_some, ite_true,
      CborRecordWorldClient.nextFits, CborProductionBoundary.nextFits] <;> rfl

/-- Beacon send refusal uses the actual established phase and its native sender before every callback. -/
theorem beacon_admission (state : PqxdhDeploymentNative.State KemSK) (owner : Nat) (plaintext : Pqxdh.Bytes) :
    CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (owner, .inl plaintext)))) (nativeShell state) =
      if CborProductionBoundary.allowed (.inr (.beaconSend owner plaintext)) state then none else some none := by
  cases found : state.native.owners[owner]? with
  | none =>
    simp only [CborRecordWorldClient.refusal, nativeShell, CborProductionBoundary.allowed,
      found, Option.bind_none, ite_true]
    rfl
  | some entry =>
    cases phase : entry.beacon.phase <;>
      simp only [CborRecordWorldClient.refusal, nativeShell, CborProductionBoundary.allowed,
        found, Option.bind_some, phase, ite_true,
        CborRecordWorldClient.nextFits, CborProductionBoundary.nextFits] <;> rfl

/-- Raw receive requests are forwarded unchanged; their native decoder remains the bounded complete-frame decoder. -/
theorem raw_admission (state : PqxdhDeploymentNative.State KemSK) (raw : Pqxdh.Bytes) (owner : Nat) :
    CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inr raw)))) (nativeShell state) = none ∧
    CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (owner, .inr raw)))) (nativeShell state) = none ∧
    CborProductionBoundary.allowed (.inr (.serverRaw raw)) state = true ∧
    CborProductionBoundary.allowed (.inr (.beaconRaw owner raw)) state = true :=
  ⟨rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.CborRecordNativeAdmission

/-- info: 'BeaconcryptCore.Computational.CborRecordNativeAdmission.server_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordNativeAdmission.server_admission

/-- info: 'BeaconcryptCore.Computational.CborRecordNativeAdmission.beacon_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordNativeAdmission.beacon_admission

/-- info: 'BeaconcryptCore.Computational.CborRecordNativeAdmission.raw_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordNativeAdmission.raw_admission
