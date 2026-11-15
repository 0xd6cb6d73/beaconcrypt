-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame
import BeaconcryptCore.Computational.RegistrationNativeKemRoster

/-! This particular native source has one indexed KEM birth per successfully appended local owner. All optional constructor failure occurs before that birth; the subsequent actual World owner allocation and local append have no failure return. The theorem derives the relation between the two separately represented indices instead of assuming their equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeKemBirthInvariant (metadata)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}

def Holds (current : State n KemSK source) : Prop :=
  current.pool.keys.length = current.beacons.length ∧
    ∀ (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source),
      current.beacons[index]? = some owner → owner.kemHandle = index

private theorem same_holds (before after : State n KemSK source) (prior : Holds before)
    (keys : after.pool.keys = before.pool.keys) (owners : after.beacons.map metadata = before.beacons.map metadata) :
    Holds after := by
  have lengthEq : after.beacons.length = before.beacons.length := by
    simpa only [List.length_map] using congrArg List.length owners
  refine ⟨by rw [keys, lengthEq]; exact prior.1, ?_⟩
  intro index owner found
  have backwards : RegistrationNativeKemRoster.Prefix after.beacons before.beacons :=
    ⟨[], by rw [owners]; simp⟩
  obtain ⟨earlier, earlierAt, same⟩ := RegistrationNativeKemRoster.lookup after.beacons before.beacons backwards index owner found
  have handle := congrArg Prod.fst same
  exact handle.symm.trans (prior.2 index earlier earlierAt)

private theorem append_holds (before after : State n KemSK source) (prior : Holds before)
    (owner : RegistrationNativeBeaconFrontend.Owner source)
    (owners : after.beacons = before.beacons ++ [owner])
    (lengthEq : after.pool.keys.length = before.pool.keys.length + 1)
    (handle : owner.kemHandle = before.beacons.length) : Holds after := by
  refine ⟨by rw [lengthEq, owners, List.length_append]; simpa only [List.length_singleton] using congrArg (fun size => size + 1) prior.1, ?_⟩
  intro index selected found
  by_cases earlier : index < before.beacons.length
  · rw [owners, List.getElem?_append_left earlier] at found
    exact prior.2 index selected found
  · have within := (List.getElem?_eq_some_iff.mp found).1
    rw [owners, List.length_append, List.length_singleton] at within
    have sameIndex : index = before.beacons.length := by omega
    subst index
    rw [owners, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at found
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst selected
    exact handle

private theorem beacon_metadata (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (localLaw : ∀ owners env result, result ∈ support ((work.run owners).run env) → result.1.2.map metadata = owners.map metadata)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    result.2.beacons.map metadata = before.beacons.map metadata := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have actual : inner.1 ∈ support ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have retained := localLaw before.beacons _ inner.1 actual
  cases returned
  exact retained

/-- Actual successful and failed bundles preserve the derived local-owner/private-handle alignment. -/
theorem bundle_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : State n KemSK source) (result : RustM (Option Pqxdh.Bytes) × State n KemSK source)
    (prior : Holds before)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run before)) : Holds result.2 :=
  same_holds before result.2 prior
    (RegistrationNativeKemPoolFrame.beacon_keys setup checks representation created _
      (RegistrationNativeKemBeaconFootprint.bundle_zero setup .create wire index) before result supported)
    (beacon_metadata setup checks representation created _
      (RegistrationNativeKemBirthLifecycle.bundle_metadata setup source wire index) before result supported)

/-- Actual finish, including private decapsulation and all rejected opens, preserves the derived alignment. -/
theorem finish_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) (before : State n KemSK source)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK source) (prior : Holds before)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before)) : Holds result.2 :=
  same_holds before result.2 prior
    (RegistrationNativeKemPoolFrame.beacon_keys setup checks representation created _
      (RegistrationNativeKemBeaconFootprint.finish_zero setup .create wire index packet) before result supported)
    (beacon_metadata setup checks representation created _
      (RegistrationNativeKemBirthLifecycle.finish_metadata setup source wire index packet) before result supported)

/-- The actual constructor increments private pool and local roster together after every pre-birth failure gate. -/
theorem create_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) (result : RustM (Option Nat) × State n KemSK source) (prior : Holds before)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) : Holds result.2 := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨outcome, reached, returned⟩ := supported
  change outcome ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
    (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) at reached
  rw [RegistrationNativeBeaconBirth.create_program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨prepared, preparedReached, continued⟩ := reached
  have keys := RegistrationNativeKemPoolFrame.program_keys setup checks representation created _
    (RegistrationNativeKemBeaconFootprint.prepare_zero .create edPin mlPin keyId before.beacons _) before prepared preparedReached
  have original : prepared.1 ∈ support
      (((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst preparedReached
  have owners := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId before.beacons _ prepared.1 original
  cases actual : prepared.1.1.1 with
  | fail error | div =>
      simp only [actual, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      cases returned
      simpa only [Holds, keys, owners] using prior
  | ok reply => cases reply with
    | none =>
        simp only [actual, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        cases returned
        simpa only [Holds, keys, owners] using prior
    | some ready =>
        simp only [actual] at continued
        rw [RegistrationNativeBeaconBirth.append_program] at continued
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff,
          simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
        obtain ⟨born, generated, allocated, allocation, terminal⟩ := continued
        obtain ⟨pair, _honest, birthReply, poolAfter⟩ := RegistrationNativeExperiment.trusted_create_generated setup checks representation created source prepared.2 born generated
        have afterAllocation := RegistrationNativeKemPoolFrame.trusted_keys setup checks representation created
          (.inl (.inr (.appendOwner keyId edPin .fresh))) (by simp [RegistrationNativeKemBeaconFootprint.counted]) born.2 allocated allocation
        cases terminal
        cases returned
        apply append_holds before _ prior
          (RegistrationNativeBeaconBirth.owner setup source ready.pin ready.identity ready.prekey born.1 allocated.1)
        · rw [owners]
        · rw [afterAllocation, poolAfter, keys, List.length_append, List.length_singleton]
        · change born.1.1 = before.beacons.length
          rw [birthReply, keys]
          exact prior.1

end BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment.bundle_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment.finish_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment.create_keeps
