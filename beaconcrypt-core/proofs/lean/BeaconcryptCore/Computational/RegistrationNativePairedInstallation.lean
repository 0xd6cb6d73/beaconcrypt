-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedDemand

/-! A reached private material demand records the very seed from which the native Server and Beacon continuations construct their consumed sequence-one kernels. Subsequent hidden World installations resolve that same persistent seed and retain the actual authenticated public AD. These receipts are derived from the actual lazy service and actual installation, without an assumed table-alias or successful-kernel equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedInstallation
open RegistrationNativePairedServices (State Ordered)
open RegistrationNativePairedDemand (readMaterial readSeed output privateDemand)
open PqxdhRecordLiftInterface
open PqxdhDeploymentHiddenLayout (Material joinOutput splitOutput)
variable {n : Nat}

/-- A private108 result carries its actual material and seed receipts in the two persistent tables. -/
theorem output_receipts (slot : Slot n) (before : State n)
    (result : PqxdhServerAuthKeySchedule.Output × State n)
    (supported : result ∈ support ((output slot).run before)) :
    result.2.materials.1 slot = some (splitOutput result.1).1 ∧
    result.2.world.seeds.1 slot = some (splitOutput result.1).2 ∧
    before.materials.1 ≤ result.2.materials.1 ∧ before.world.seeds.1 ≤ result.2.world.seeds.1 ∧
    result.2.slots = before.slots ∧ result.2.next = before.next ∧
    result.2.demands = before.demands := by
  simp only [output, StateT.run_bind, StateT.run_pure, support_bind,
    Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨material, materialReached, seed, seedReached, rfl⟩ := supported
  have mat := RegistrationNativePairedDemand.readMaterial_facts slot before material materialReached
  have gen := RegistrationNativePairedDemand.readSeed_facts slot material.2 seed seedReached
  simp only [PqxdhDeploymentHiddenLayout.split_join]
  exact ⟨by rw [gen.2.2.1]; exact mat.1, gen.1,
    by rw [gen.2.2.1]; exact mat.2.1,
    by rw [mat.2.2.1] at gen; exact gen.2.1,
    gen.2.2.2.1.trans mat.2.2.2.1,
    gen.2.2.2.2.1.trans mat.2.2.2.2.1,
    gen.2.2.2.2.2.1.trans mat.2.2.2.2.2.1⟩

/-- The canonical literal-input slot and both concrete byte receipts are produced by the actual demand, including on a repeated cross-role alias. -/
theorem demand_receipts (bytes : Pqxdh.Bytes) (before after : State n)
    (slot : Slot n) (value : PqxdhServerAuthKeySchedule.Output)
    (supported : (some (slot, value), after) ∈ support ((privateDemand bytes).run before)) :
    after.slots bytes = some slot ∧ after.materials.1 slot = some (splitOutput value).1 ∧
    after.world.seeds.1 slot = some (splitOutput value).2 ∧
    before.materials.1 ≤ after.materials.1 ∧ before.world.seeds.1 ≤ after.world.seeds.1 ∧
    after.demands = before.demands + 1 ∧ before.next ≤ after.next ∧ after.next ≤ before.next + 1 := by
  unfold privateDemand at supported
  change (some (slot, value), after) ∈ support
    (match (RegistrationNativePairedServices.reserve bytes before).1 with
    | none => pure (none, (RegistrationNativePairedServices.reserve bytes before).2)
    | some selected => _) at supported
  cases assigned : (RegistrationNativePairedServices.reserve bytes before).1 with
  | none => simp only [assigned, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported; cases supported.1
  | some selected =>
    simp only [assigned, support_map] at supported
    obtain ⟨⟨actual, final⟩, reached, equal⟩ := supported
    cases equal
    have receipts := output_receipts slot (RegistrationNativePairedServices.reserve bytes before).2
      (actual, final) reached
    have reservation := RegistrationNativePairedServices.reserve_receipt bytes before
    refine ⟨?_, receipts.1, receipts.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [receipts.2.2.2.2.1]
      exact RegistrationNativePairedServices.reserve_records bytes before slot assigned
    · rw [reservation.2.2.1] at receipts
      exact receipts.2.2.1
    · rw [reservation.2.1] at receipts
      exact receipts.2.2.2.1
    · exact receipts.2.2.2.2.2.2.trans reservation.1
    · rw [receipts.2.2.2.2.2.1]
      exact reservation.2.2.2.1
    · rw [receipts.2.2.2.2.2.1]
      exact reservation.2.2.2.2

/-- Material and seed evaluation cannot add a second allocation or demand to the one reservation. -/
theorem demand_clock (bytes : Pqxdh.Bytes) (before : State n)
    (result : Option (Slot n × PqxdhServerAuthKeySchedule.Output) × State n)
    (supported : result ∈ support ((privateDemand bytes).run before)) :
    result.2.slots = (RegistrationNativePairedServices.reserve bytes before).2.slots ∧
    result.2.next = (RegistrationNativePairedServices.reserve bytes before).2.next ∧
    result.2.demands = before.demands + 1 := by
  unfold privateDemand at supported
  change result ∈ support
    (match (RegistrationNativePairedServices.reserve bytes before).1 with
    | none => pure (none, (RegistrationNativePairedServices.reserve bytes before).2)
    | some selected => _) at supported
  cases assigned : (RegistrationNativePairedServices.reserve bytes before).1 with
  | none =>
    simp only [assigned, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨rfl, rfl, (RegistrationNativePairedServices.reserve_receipt bytes before).1⟩
  | some slot =>
    simp only [assigned, support_map] at supported
    obtain ⟨⟨value, after⟩, reached, equal⟩ := supported
    cases equal
    have receipts := output_receipts slot (RegistrationNativePairedServices.reserve bytes before).2
      (value, after) reached
    exact ⟨receipts.2.2.2.2.1, receipts.2.2.2.2.2.1,
      receipts.2.2.2.2.2.2.trans (RegistrationNativePairedServices.reserve_receipt bytes before).1⟩

/-- First-touch slot indices remain bounded by actual material demands, including failed publications and overflow. -/
theorem demand_ordered (bytes : Pqxdh.Bytes) (before : State n) (ordered : Ordered before)
    (result : Option (Slot n × PqxdhServerAuthKeySchedule.Output) × State n)
    (supported : result ∈ support ((privateDemand bytes).run before)) : Ordered result.2 := by
  have clock := demand_clock bytes before result supported
  have reservation := RegistrationNativePairedServices.reserve_ordered bytes before ordered
  unfold Ordered at reservation ⊢
  rw [clock.1, clock.2.1, clock.2.2,
    ← (RegistrationNativePairedServices.reserve_receipt bytes before).1]
  exact reservation

/-- The real source Server insertion uses the complete generated kernel retained by a reached paired service, and its exact native binding AD. -/
theorem server_install (bytes : Pqxdh.Bytes) (before reached : State n)
    (slot : Slot n) (value : PqxdhServerAuthKeySchedule.Output)
    (demanded : (some (slot, value), reached) ∈ support ((privateDemand bytes).run before))
    (keyId : U64) (binding : PeerBinding) (after : PqxdhRecordLiftWorld.State n)
    (installed : (true, after) ∈ support
      ((PqxdhRecordLiftWorld.installServer keyId binding (.hidden slot)).run reached.world)) :
    ∃ (server : PqxdhRecordLiftWorld.Server) (peer : RawCtxServerRouting.Peer (Std.Array U8 151#usize)),
      after.server = some server ∧ server.records.server.peers keyId = some peer ∧
      peer.kernel = PqxdhRecordLiftWorld.kernel .server (splitOutput value).2 ∧
      peer.metadata = binding.associatedArray server.records.server.identity :=
  RegistrationHiddenInstall.installed_cached_kernel keyId binding slot (splitOutput value).2 reached.world after
    (demand_receipts bytes before reached slot value demanded).2.2.1 installed

/-- Actual Beacon hidden insertion keeps the completed native shell and the exact same seed already consumed by its paired service. No role can reset the seed after the other role's first use. -/
theorem beacon_install (bytes : Pqxdh.Bytes) (before reached : State n)
    (slot : Slot n) (value : PqxdhServerAuthKeySchedule.Output)
    (demanded : (some (slot, value), reached) ∈ support ((privateDemand bytes).run before))
    (owner : Nat) (shell : BeaconShell) (after : PqxdhRecordLiftWorld.State n)
    (installed : (true, after) ∈ support
      ((PqxdhRecordLiftWorld.installBeacon owner shell (.hidden slot)).run reached.world)) :
    after.owners = reached.world.owners.set owner
      (.established shell (PqxdhRecordLiftWorld.kernel .beacon (splitOutput value).2)) ∧
    after.used slot .beacon = true ∧
    after.seeds.1 slot = some (splitOutput value).2 := by
  have cached := (demand_receipts bytes before reached slot value demanded).2.2.1
  have admitted := PqxdhRecordLiftWorld.installBeacon_admitted owner shell (.hidden slot)
    reached.world after installed
  have marked := PqxdhRecordLiftWorld.installBeacon_marks owner shell slot reached.world after installed
  have hit := PqxdhRecordLiftWorld.resolve_hit .beacon slot reached.world (splitOutput value).2 cached
  simp only [StateT.run] at hit
  simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run, ite_eq_left admitted, hit,
    pure_bind, support_pure, Set.mem_singleton_iff] at installed
  cases installed
  exact ⟨rfl, marked, cached⟩

/-- The actual native Server continuation's entire published kernel is precisely the kernel installed by the paired hidden capability. -/
theorem server_native_kernel {Encoded : Type} (bytes : Pqxdh.Bytes) (before reached : State n)
    (slot : Slot n) (value : PqxdhServerAuthKeySchedule.Output)
    (demanded : (some (slot, value), reached) ∈ support ((privateDemand bytes).run before))
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (published : registration.PublishedServerResponse Encoded)
    (completed : .ok (.Ok published) ∈ support (RegistrationBoundPublication.program encode initial value))
    (keyId : U64) (binding : PeerBinding) (after : PqxdhRecordLiftWorld.State n)
    (installed : (true, after) ∈ support
      ((PqxdhRecordLiftWorld.installServer keyId binding (.hidden slot)).run reached.world)) :
    ∃ (server : PqxdhRecordLiftWorld.Server) (peer : RawCtxServerRouting.Peer (Std.Array U8 151#usize)),
      after.server = some server ∧ server.records.server.peers keyId = some peer ∧
      peer.kernel = published.kernel ∧ peer.metadata = binding.associatedArray server.records.server.identity := by
  obtain ⟨server, peer, present, stored, kernel, data⟩ :=
    server_install bytes before reached slot value demanded keyId binding after installed
  have native := RegistrationBoundPublication.published_kernel encode initial
    (splitOutput value).1 (splitOutput value).2 published
    (by simpa only [PqxdhDeploymentHiddenLayout.join_split] using completed)
  exact ⟨server, peer, present, stored, kernel.trans native.symm, data⟩

/-- The actual native Beacon continuation's entire consumed kernel is the one installed by the paired capability, including sequence counters and receive cache. -/
theorem beacon_native_kernel {Auxiliary : Type} (bytes : Pqxdh.Bytes) (before reached : State n)
    (slot : Slot n) (value : PqxdhServerAuthKeySchedule.Output)
    (demanded : (some (slot, value), reached) ∈ support ((privateDemand bytes).run before))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (completed : registration.CompletedBeacon)
    (primitiveBefore primitiveAfter : RawCtxSharedPrimitive.SharedState Auxiliary)
    (executed : (.ok (.Ok completed), primitiveAfter) ∈ support
      ((RegistrationBeaconBoundSource.fromOutput source writer descriptor value).run primitiveBefore))
    (owner : Nat) (shell : BeaconShell) (after : PqxdhRecordLiftWorld.State n)
    (installed : (true, after) ∈ support
      ((PqxdhRecordLiftWorld.installBeacon owner shell (.hidden slot)).run reached.world)) :
    after.owners = reached.world.owners.set owner (.established shell completed.kernel) := by
  have native := RegistrationBeaconSeed.completed_kernel source writer descriptor
    (splitOutput value).1 (splitOutput value).2 completed primitiveBefore primitiveAfter
    (by simpa only [PqxdhDeploymentHiddenLayout.join_split] using executed)
  exact (beacon_install bytes before reached slot value demanded owner shell after installed).1.trans
    (congrArg (fun kernel => reached.world.owners.set owner (.established shell kernel)) native.symm)

/-- The actual retained native completion, rather than a recomputed legacy transcript, supplies installed public AD. -/
def beaconShell (identityKeyId : U64) (completed : registration.CompletedBeacon) : BeaconShell :=
  ⟨identityKeyId, completed.control, completed.binding.associated_data⟩

/-- Failed source opening retains its exact failure; successful opening requests only the private slot and carries its actual public completed fields. -/
def beaconAfter (owner : Nat) (identityKeyId : U64) (slot : Slot n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) : OracleComp (EnvEffects n)
      (RustM (core.result.Result (Bool × RegistrationBeaconSeed.PublicCompleted) pqxdh.BeaconAborted)) :=
  match result with
  | .ok (.Ok completed) => do
      let installed ← (EnvEffects n).query (.inr (.installBeacon owner (beaconShell identityKeyId completed) (.hidden slot)))
      pure (.ok (.Ok (installed, ⟨completed.control, completed.binding, completed.application⟩)))
  | .ok (.Err aborted) => pure (.ok (.Err aborted))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Hidden publication never passes the placeholder or real concrete Beacon kernel to the public capability. -/
theorem beaconAfter_replace (owner : Nat) (identityKeyId : U64) (slot : Slot n)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    beaconAfter owner identityKeyId slot (RegistrationBeaconSeed.replace kernel result) =
      beaconAfter owner identityKeyId slot result := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePairedInstallation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.output_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.output_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.demand_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.demand_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.server_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.server_install
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.beacon_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.beacon_install
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.server_native_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.server_native_kernel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.beacon_native_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.beacon_native_kernel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.beaconAfter_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.beaconAfter_replace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.demand_clock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.demand_clock
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedInstallation.demand_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedInstallation.demand_ordered
