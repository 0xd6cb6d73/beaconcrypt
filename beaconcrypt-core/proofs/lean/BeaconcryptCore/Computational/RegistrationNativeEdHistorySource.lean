-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdHistory
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners

/-! Actual source wrapper receipts transport fixed-prekey signing histories through construction and outgoing bundle calls. The primitive interpreter and final record World remain the same; only the source control flow and explicit private history field are inspected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEdHistorySource
open RegistrationNativeBeaconFrontend
open RegistrationNativeEdHistory (Fixed Preserves)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

theorem fixed_empty (source : RegistrationNativeMldsa.Source) : Fixed ([] : State source) := by
  intro owner member
  cases member

theorem create_fixed (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Preserves (n := n) (Auxiliary := Auxiliary) Fixed (create setup source edPin mlPin keyId) := by
  intro owners env result prior supported
  rw [RegistrationNativeBeaconBirth.create_program, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨prepared, beforeOwners⟩, beforeEnv⟩, earlier, continued⟩ := supported
  have same : beforeOwners = owners := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env _ earlier
  cases prepared with
  | fail error =>
      simp only [support_pure, Set.mem_singleton_iff] at continued
      cases continued
      simpa only [same] using prior
  | div =>
      simp only [support_pure, Set.mem_singleton_iff] at continued
      cases continued
      simpa only [same] using prior
  | ok selected => cases selected with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at continued
        cases continued
        simpa only [same] using prior
    | some prepared =>
        change result ∈ support (((appendBorn setup source edPin keyId prepared.pin
          prepared.identity prepared.prekey).run beforeOwners).run beforeEnv) at continued
        rw [RegistrationNativeBeaconBirth.append_program] at continued
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continued
        obtain ⟨born, _, ⟨worldOwner, _, returned⟩⟩ := continued
        have ownersEq := congrArg (fun result => result.1.2) returned
        rw [ownersEq]
        intro current member
        rcases List.mem_append.mp member with old | fresh
        · exact prior current (same ▸ old)
        · simp only [List.mem_singleton] at fresh
          cases fresh
          exact RegistrationNativeEdOrigin.fixed_empty _

/-- Any locally proved owner-history invariant transfers through the actual source wrapper with its full reached primitive/World state. -/
theorem source_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    {Value : Type} (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (invariant : State source → Prop) (law : Preserves invariant work)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (prior : invariant before.beacons)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    invariant result.2.beacons := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨⟨⟨⟨value, ownersAfter⟩, envAfter⟩, sourceAfter⟩, interpreted, returned⟩ := supported
  have raw : ((value, ownersAfter), envAfter) ∈ support
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst interpreted
  have kept := law before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) _ prior raw
  have same : result.2.beacons = ownersAfter := congrArg (fun result => result.2.beacons) returned
  exact same.symm ▸ kept

theorem source_create_fixed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK source)
    (prior : Fixed before.beacons)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (create setup source edPin mlPin keyId)).run before)) : Fixed result.2.beacons :=
  source_preserves setup checks representation created source _ Fixed (create_fixed setup source edPin mlPin keyId) before result prior supported

theorem source_bundle_fixed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source)
    (prior : Fixed before.beacons)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (bundle setup source wire index)).run before)) : Fixed result.2.beacons :=
  source_preserves setup checks representation created source _ Fixed
    (RegistrationNativeEdHistory.bundle_fixed setup source wire index) before result prior supported

theorem source_finish_fixed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source)
    (prior : Fixed before.beacons)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (finish setup source wire index packet)).run before)) : Fixed result.2.beacons :=
  source_preserves setup checks representation created source _ Fixed
    (RegistrationNativeEdHistory.finish_fixed setup source wire index packet) before result prior supported

end BeaconcryptCore.Computational.RegistrationNativeEdHistorySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.fixed_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.fixed_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.create_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.create_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_create_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_create_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_bundle_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_bundle_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_finish_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistorySource.source_finish_fixed
