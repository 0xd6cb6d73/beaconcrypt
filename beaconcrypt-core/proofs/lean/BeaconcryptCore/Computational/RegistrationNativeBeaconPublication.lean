-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
import BeaconcryptCore.Computational.RegistrationNativeKemPublication
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! The concrete Beacon wrapper preserves the actual outgoing writer receipt. Projecting private interpreter states only shrinks support; it does not replace the native signing, fingerprint, transcript or publication continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
open RegistrationNativeBeaconFrontend
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeWire (Wire)
variable {ι κ KemSK Auxiliary Private Value : Type} {base : OracleSpec ι} {spec : OracleSpec κ} {n : Nat}

theorem nested_support (mlSource : RegistrationNativeMldsa.Source)
    (implementation : QueryImpl spec (M n KemSK mlSource Auxiliary)) (work : OracleComp spec Value)
    (owners ownersAfter : State mlSource) (env envAfter : EnvState Auxiliary) (value : Value)
    (reached : ((value, ownersAfter), envAfter) ∈ support (((simulateQ implementation work).run owners).run env)) :
    value ∈ support work := by
  apply OracleComp.support_simulateQ_run'_subset implementation.flattenStateT work (owners, env)
  rw [StateT.run'_eq, OracleComp.simulateQ_flattenStateT_run, bind_pure_comp]
  simp only [Functor.map_map, support_map]
  exact ⟨((value, ownersAfter), envAfter), reached, rfl⟩

theorem pq_key (bytes : PqxdhKemIndCca.MlKem768PublicKey) :
    RegistrationRootInput.pqKey (pqArray bytes) = bytes := by
  apply Subtype.ext
  simp [RegistrationRootInput.pqKey, pqArray, absBytes, List.map_map, Function.comp_def]

theorem outgoing_key (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (selected : Owner mlSource) (oneTime : ScalarBytes)
    (owners ownersAfter : State mlSource) (env envAfter : EnvState Auxiliary)
    (published : registration.PublishedBeaconInit Pqxdh.Bytes)
    (reached : ((.ok (.Ok published), ownersAfter), envAfter) ∈ support
      (((simulateQ (outgoing (n := n) setup mlSource index selected)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨selected.pin.binding⟩ (inputs setup selected)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ selected.pin selected.mldsa.publicKey)).run owners).run env)) :
    RegistrationNativeKemPublication.PublishedKey wire.encodeInit selected.kemPublic published := by
  have original := nested_support mlSource (outgoing setup mlSource index selected)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨selected.pin.binding⟩ (inputs setup selected)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ selected.pin selected.mldsa.publicKey)
    owners ownersAfter env envAfter (.ok (.Ok published)) reached
  simpa only [inputs, pq_key] using RegistrationNativeKemPublication.begin_key wire.encodeInit
    ⟨selected.pin.binding⟩ (inputs setup selected)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ selected.pin selected.mldsa.publicKey published original

theorem bundle_key (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (owners ownersAfter : State mlSource) (env envAfter : EnvState Auxiliary)
    (bytes : Pqxdh.Bytes)
    (reached : ((.ok (some bytes), ownersAfter), envAfter) ∈ support
      (((bundle (n := n) setup mlSource wire index).run owners).run env)) :
    ∃ selected published, owners[index]? = some selected ∧ published.encoded = bytes ∧
      RegistrationNativeKemPublication.PublishedKey wire.encodeInit selected.kemPublic published := by
  obtain ⟨selected, oneTime, published, beforeOwners, beforeEnv, duringOwners, duringEnv,
    found, encoded, called⟩ := RegistrationNativeKemBirthOwners.bundle_receipt
      setup mlSource wire index owners env bytes ownersAfter envAfter reached
  exact ⟨selected, published, found, encoded,
    outgoing_key setup mlSource wire index selected oneTime beforeOwners duringOwners beforeEnv duringEnv published called⟩

/-- The full source wrapper's public encoded Init recovers its actual original owner's PQ input under the native wire readback contract. -/
theorem source_bundle_key (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (mlSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (readback : RegistrationNativeWire.InitReadBack wire) (index : Nat)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (bytes : Pqxdh.Bytes)
    (reached : (.ok (some bytes), after) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation created
        (bundle setup mlSource wire index)).run before)) :
    ∃ selected packet, before.beacons[index]? = some selected ∧
      RegistrationNativeWire.readInit wire bytes = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet selected.kemPublic := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨⟨⟨⟨value, ownersAfter⟩, envAfter⟩, sourceAfter⟩, interpreted, returned⟩ := reached
  have valueEq : value = .ok (some bytes) := congrArg Prod.fst returned.symm
  subst value
  have original : ((.ok (some bytes), ownersAfter), envAfter) ∈ support
      (((bundle (n := n) setup mlSource wire index).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst interpreted
  obtain ⟨selected, published, found, encoded, receipt⟩ := bundle_key setup mlSource wire index _ _ _ _ bytes original
  obtain ⟨packet, decoded, sameKey⟩ := RegistrationNativeKemPublication.decoded_key wire readback selected.kemPublic published receipt
  exact ⟨selected, packet, found, encoded ▸ decoded, sameKey⟩

end BeaconcryptCore.Computational.RegistrationNativeBeaconPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.nested_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.nested_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.pq_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.pq_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.outgoing_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.outgoing_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.bundle_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.bundle_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.source_bundle_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPublication.source_bundle_key
