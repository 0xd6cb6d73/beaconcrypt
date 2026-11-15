-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconCounter
import BeaconcryptCore.Computational.RegistrationNativeOptionalSupport
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle

/-! Actual candidate-provider Beacon calls retain a result of the literal native owner controller. Its pure metadata and publication receipts therefore apply directly, without replacing any candidate callback by a real-mode SDK execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenFrame (lower)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Every actual open Beacon call retains its interpreted owner-controller result and complete private service poststate before the final local roster installation. -/
theorem beacon_callback (chosen : Bool)
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (before after : State n mlSource KemSK) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon work))).run).run before)) :
    ∃ result reached,
      (some result, reached) ∈ support
        (((simulateQ ((provider ∘ₛ lower chosen) ∘ₛ RegistrationNativeKemBeaconCompiler.trusted)
          ((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.server.world))).run).run
            ((RegistrationNativeKemServerState.mask before.1.1, before.1.2), before.2)) ∧
      value = result.1.1 ∧ after.1.1.beacons = result.1.2 ∧ after.1.2 = reached.1.2 ∧ after.2 = reached.2 := by
  simp only [RegistrationNativeKemBeaconCompiler.beacon, RegistrationNativeKemServerInterface.get,
    RegistrationNativeKemServerInterface.put, simulateQ_bind, simulateQ_spec_query, lower,
    QueryImpl.apply_compose, RegistrationNativeKemFrontendInterface.lift, RegistrationNativeKemRouting.route,
    OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
  rw [RegistrationNativeKemOpenProvider.get_run] at supported
  simp only [pure_bind, Option.elim_some, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
  cases reply with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some reply =>
      have sameOwners : (RegistrationNativeKemServerState.mask before.1.1).beacons = before.1.1.beacons := rfl
      have sameEnv : RegistrationWorldAgreementCompiler.erase (RegistrationNativeKemServerState.mask before.1.1).server.world =
          RegistrationWorldAgreementCompiler.erase before.1.1.server.world := rfl
      rw [sameOwners, sameEnv] at called
      have callback : (some reply, reached) ∈ support
          (((simulateQ ((provider ∘ₛ lower chosen) ∘ₛ RegistrationNativeKemBeaconCompiler.trusted)
            ((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.server.world))).run).run
              ((RegistrationNativeKemServerState.mask before.1.1, before.1.2), before.2)) := by
        simpa only [lower, QueryImpl.simulateQ_compose] using called
      simp only [Option.elim_some, StateT.run_bind] at tail
      rw [RegistrationNativeKemOpenProvider.get_run] at tail
      simp only [pure_bind, Option.elim_some, StateT.run_bind] at tail
      rw [RegistrationNativeKemOpenProvider.put_run] at tail
      simp only [pure_bind, Option.elim_some] at tail
      have valueEq := congrArg Prod.fst tail
      change some value = some reply.1.1 at valueEq
      have ownersEq := congrArg (fun result => result.2.1.1.beacons) tail
      change after.1.1.beacons = reply.1.2 at ownersEq
      have privateEq := congrArg (fun result => result.2.1.2) tail
      change after.1.2 = reached.1.2 at privateEq
      have phaseEq := congrArg (fun result => result.2.2) tail
      change after.2 = reached.2 at phaseEq
      exact ⟨reply, reached, callback, Option.some.inj valueEq, ownersEq, privateEq, phaseEq⟩

/-- Every completed actual open Beacon call has a supported original controller result and installs exactly its reached owner roster. -/
theorem beacon_result (chosen : Bool)
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (before after : State n mlSource KemSK) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon work))).run).run before)) :
    ∃ result, result ∈ support ((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.server.world)) ∧
      value = result.1.1 ∧ after.1.1.beacons = result.1.2 := by
  obtain ⟨result, reached, callback, sameValue, ownersEq, _privateEq, _phaseEq⟩ :=
    beacon_callback setup checks wire route representation created credential selected pairs publicKey real chosen work before after value supported
  exact ⟨result, RegistrationNativeOptionalSupport.completed_support _ _ result _ reached callback, sameValue, ownersEq⟩

/-- Actual candidate-provider bundles, including failures, preserve the original owner's retained private handle and PQ key metadata. -/
theorem bundle_metadata (chosen : Bool) (index : Nat) (before after : State n mlSource KemSK)
    (value : RustM (Option Pqxdh.Bytes))
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon
        (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index)))).run).run before)) :
    after.1.1.beacons.map RegistrationNativeKemBirthInvariant.metadata =
      before.1.1.beacons.map RegistrationNativeKemBirthInvariant.metadata := by
  obtain ⟨result, original, _sameValue, ownersEq⟩ := beacon_result setup checks wire route representation created credential
    selected pairs publicKey real chosen _ before after value supported
  rw [ownersEq]
  exact RegistrationNativeKemBirthLifecycle.bundle_metadata setup mlSource wire index before.1.1.beacons _ result original

/-- Actual candidate-provider finishes preserve that same retained birth metadata through every authentication, decapsulation and record outcome. -/
theorem finish_metadata (chosen : Bool) (index : Nat) (packet : Option registration.ResponsePacket)
    (before after : State n mlSource KemSK) (value : RustM (Option Pqxdh.Bytes))
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon
        (RegistrationNativeBeaconFrontend.finish setup mlSource wire index packet)))).run).run before)) :
    after.1.1.beacons.map RegistrationNativeKemBirthInvariant.metadata =
      before.1.1.beacons.map RegistrationNativeKemBirthInvariant.metadata := by
  obtain ⟨result, original, _sameValue, ownersEq⟩ := beacon_result setup checks wire route representation created credential
    selected pairs publicKey real chosen _ before after value supported
  rw [ownersEq]
  exact RegistrationNativeKemBirthLifecycle.finish_metadata setup mlSource wire index packet before.1.1.beacons _ result original

/-- A literal successful candidate-provider bundle publishes the exact PQ key of its original current owner under native bounded readback. -/
theorem bundle_key (readback : RegistrationNativeWire.InitReadBack wire) (chosen : Bool) (index : Nat)
    (before after : State n mlSource KemSK) (bytes : Pqxdh.Bytes)
    (supported : (some (.ok (some bytes)), after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon
        (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index)))).run).run before)) :
    ∃ owner packet, before.1.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire bytes = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.kemPublic := by
  obtain ⟨⟨⟨reply, owners⟩, env⟩, original, sameValue, _ownersEq⟩ := beacon_result setup checks wire route representation created credential
    selected pairs publicKey real chosen (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index)
      before after (.ok (some bytes)) supported
  cases sameValue
  obtain ⟨owner, published, found, encoded, receipt⟩ := RegistrationNativeBeaconPublication.bundle_key setup mlSource wire index _ _ _ _ bytes original
  obtain ⟨packet, decoded, sameKey⟩ := RegistrationNativeKemPublication.decoded_key wire readback owner.kemPublic published receipt
  exact ⟨owner, packet, found, encoded ▸ decoded, sameKey⟩

end BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.beacon_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.beacon_result
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.beacon_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.beacon_callback
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.bundle_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.bundle_metadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.finish_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.finish_metadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.bundle_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult.bundle_key
