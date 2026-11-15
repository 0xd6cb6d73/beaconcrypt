-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource

/-! The actual source Beacon wrappers preserve initialized private generated-key ownership. Birth appends its actual supported generator result; all prior handles persist. Bundle, response authentication, private decapsulation and initial-record opening retain the concrete handle/public-key metadata on every success and failure path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemBirthInvariant (Holds Owns metadata)
open RegistrationNativeExperiment (State)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem beacon_keeps_metadata (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (localLaw : ∀ owners env result, result ∈ support ((work.run owners).run env) →
      result.1.2.map metadata = owners.map metadata)
    (before after : State n KemSK mlSource) (reply : Value)
    (prior : Holds setup before.beacons before.pool)
    (supported : (reply, after) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    Holds setup after.beacons after.pool := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨result, reached, returned⟩ := supported
  have preserved := RegistrationNativeKemBirthInvariant.trusted_program setup checks representation created mlSource
    before.beacons _ before result.2 result.1 prior reached
  have native : result.1 ∈ support
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have retained := localLaw _ _ result.1 native
  cases returned
  exact ⟨preserved.1, RegistrationNativeKemBirthInvariant.metadata_transport
    before.beacons result.1.1.2 result.2.pool preserved.2 retained⟩

/-- The actual source bundle preserves the complete initialized owner-to-private-key relation on every outcome. -/
theorem bundle_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before after : State n KemSK mlSource) (reply : RustM (Option Pqxdh.Bytes))
    (prior : Holds setup before.beacons before.pool)
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index)).run before)) :
    Holds setup after.beacons after.pool :=
  beacon_keeps_metadata setup checks representation created _
    (RegistrationNativeKemBirthLifecycle.bundle_metadata setup mlSource wire index) before after reply prior supported

/-- Actual finish rejection, abort, successful private decapsulation and record installation retain every generated owner binding. -/
theorem finish_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option beaconcrypt_core.registration.ResponsePacket)
    (before after : State n KemSK mlSource) (reply : RustM (Option Pqxdh.Bytes))
    (prior : Holds setup before.beacons before.pool)
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup mlSource wire index packet)).run before)) :
    Holds setup after.beacons after.pool :=
  beacon_keeps_metadata setup checks representation created _
    (RegistrationNativeKemBirthLifecycle.finish_metadata setup mlSource wire index packet) before after reply prior supported

/-- The complete actual constructor appends a genuinely generated owner while retaining every earlier owner's exact indexed secret. -/
theorem create_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : State n KemSK mlSource) (reply : RustM (Option Nat))
    (prior : Holds setup before.beacons before.pool)
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId)).run before)) :
    Holds setup after.beacons after.pool := by
  have original := supported
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨result, reached, returned⟩ := supported
  have preserved := RegistrationNativeKemBirthInvariant.trusted_program setup checks representation created mlSource
    before.beacons _ before result.2 result.1 prior reached
  have native : result.1 ∈ support
      (((RegistrationNativeBeaconFrontend.create (n := n) setup mlSource edPin mlPin keyId).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have shape := RegistrationNativeKemBirthCreateShape.create_shape setup mlSource edPin mlPin keyId before.beacons
    (RegistrationWorldAgreementCompiler.erase before.server.world) result.1.1.1 result.1.1.2 result.1.2 native
  cases returned
  change Holds setup result.1.1.2 result.2.pool
  refine ⟨preserved.1, ?_⟩
  cases value : result.1.1.1 with
  | fail error | div =>
      simp only [RegistrationNativeKemBirthCreateShape.Shape, value] at shape
      simpa only [shape] using preserved.2
  | ok answer => cases answer with
    | none =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, value] at shape
        simpa only [shape] using preserved.2
    | some index =>
        rw [value] at original
        obtain ⟨pair, _, selected, selectedAt, publicKey, privateKey⟩ :=
          RegistrationNativeBeaconBirthSource.owner_generated setup checks representation created mlSource
            edPin mlPin keyId before _ index original
        simp only [RegistrationNativeKemBirthCreateShape.Shape, value] at shape
        obtain ⟨indexEq, born, appended⟩ := shape
        have bornAt : result.1.1.2[index]? = some born := by
          rw [appended, indexEq, List.getElem?_concat_length]
        have same : selected = born := Option.some.inj (selectedAt.symm.trans bornAt)
        subst selected
        intro owner member
        rw [appended, List.mem_append, List.mem_singleton] at member
        rcases member with earlier | rfl
        · exact preserved.2 owner earlier
        · exact ⟨pair, privateKey, publicKey.symm⟩

end BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant.bundle_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant.finish_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant.create_keeps
