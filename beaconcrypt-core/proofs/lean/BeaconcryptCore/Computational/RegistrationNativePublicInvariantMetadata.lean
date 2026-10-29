-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInvariantStartup

/-! Actual public owner commands preserve pending coherence and the empty record-request analysis field together. These are local open-client invariants, independent of the chosen root or KEM interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicFrontend (State M beacon)
open RegistrationNativePublicInvariantOwners (Coherent)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Good (before : State source) : Prop := Coherent before.beacons ∧ before.environment.recordRequests = []

private theorem beacon_good
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (keeps : ∀ roster env result, Coherent roster →
      result ∈ support ((work.run roster).run env) →
      Coherent result.1.2 ∧ result.2.recordRequests = env.recordRequests)
    (before : State source) (result : Value × State source) (valid : Good before)
    (supported : result ∈ support ((beacon work).run before)) : Good result.2 := by
  simp only [beacon, StateT.run, support_map] at supported
  obtain ⟨reached, member, equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  obtain ⟨coherent, records⟩ := keeps before.beacons before.environment reached valid.1 native
  cases equal
  exact ⟨coherent, records.trans valid.2⟩

/-- Creation establishes a fresh public owner and retains all earlier pending coherence and the exact empty analysis field. -/
theorem create_good (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State source) (result : RustM (Option Nat) × State source) (valid : Good before)
    (supported : result ∈ support ((beacon
      (RegistrationNativePublicOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId)).run before)) :
    Good result.2 := by
  apply beacon_good _ _ before result valid supported
  intro roster env reached coherent member
  exact ⟨RegistrationNativePublicInvariantOwners.create_coherent setup selected publicPrekey edPin mlPin keyId roster env reached coherent member,
    RegistrationNativePublicInvariantRequests.public_create_keeps setup selected publicPrekey edPin mlPin keyId roster env reached member⟩

/-- Actual signing and publication retain both metadata invariants, including every failed writer outcome. -/
theorem bundle_good (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (before : State source) (result : RustM (Option Pqxdh.Bytes) × State source) (valid : Good before)
    (supported : result ∈ support ((beacon
      (RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey index)).run before)) :
    Good result.2 := by
  apply beacon_good _ _ before result valid supported
  intro roster env reached coherent member
  exact ⟨RegistrationNativePublicInvariantOwners.bundle_coherent setup wire selected publicPrekey index roster env reached coherent member,
    RegistrationNativePublicInvariantRequests.public_bundle_keeps setup wire selected publicPrekey index roster env reached member⟩

/-- Incoming finish preserves the actual metadata invariants before any source-game interpretation or event designation. -/
theorem finish_good (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State source) (result : RustM (Option Pqxdh.Bytes) × State source) (valid : Good before)
    (supported : result ∈ support ((beacon
      (RegistrationNativePublicOwners.finish (n := n) setup source index packet)).run before)) :
    Good result.2 := by
  apply beacon_good _ _ before result valid supported
  intro roster env reached coherent member
  exact ⟨RegistrationNativePublicInvariantFinish.finish_coherent setup index packet roster env reached coherent member,
    RegistrationNativeOrdinaryFinishSourceRequests.finish_keeps setup index packet roster env reached member⟩

end BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata.create_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata.create_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata.bundle_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata.bundle_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata.finish_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata.finish_good
