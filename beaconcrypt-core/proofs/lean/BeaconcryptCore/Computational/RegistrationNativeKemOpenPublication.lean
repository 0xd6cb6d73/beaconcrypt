-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun

/-! A successful literal raw bundle under the candidate provider publishes exactly the genuine pair at its actual local-owner/birth index. Native decoding and the actual signed PQ suffix are retained; incoming accepted packets are not restricted to unchanged bundle bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenPublication
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenBirth (borns)
open RegistrationNativeKemOpenRoster (Holds)
open RegistrationNativeKemOpenFrame (lower)
open PqxdhKemIndCca
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real
local notation "native" => RegistrationNativeKemOpenRawCounter.native (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed
attribute [local irreducible] RegistrationNativeKemOpenProvider.implementation RegistrationNativeKemParsedRouting.handler

private theorem raw_bundle_success (index : Nat) (bytes : Pqxdh.Bytes) (before after : State n mlSource KemSK)
    (supported : (some (some bytes), after) ∈ support (((native (.inr (.bundle index))).run).run before)) :
    (some (.ok (some bytes)), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed (.inr (.bundle index)))).run).run before) := by
  simp only [RegistrationNativeKemOpenRawCounter.native, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_map,
    simulateQ_spec_query, OptionT.run_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reached⟩, called, equal⟩ := supported
  cases reply with
  | none =>
      have impossible := congrArg Prod.fst equal
      simp only [Option.map_none, reduceCtorEq] at impossible
  | some reply =>
      cases reply with
      | fail error | div =>
          simp only [Option.map_some, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq,
            Option.some.injEq, reduceCtorEq, false_and] at equal
      | ok reply =>
          simp only [Option.map_some, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq,
            Option.some.injEq] at equal
          obtain ⟨rfl, rfl⟩ := equal
          exact called

/-- Actual successful raw publication identifies the genuine reserved pair at the same derived local owner and private birth coordinate. -/
theorem bundle_key (readback : RegistrationNativeWire.InitReadBack wire) (index : Nat) (bytes : Pqxdh.Bytes)
    (before after : State n mlSource KemSK) (prior : Holds pairs before)
    (supported : (some (some bytes), after) ∈ support (((native (.inr (.bundle index))).run).run before)) :
    ∃ pair packet, pairs[index]? = some pair ∧ index < borns before ∧
      RegistrationNativeWire.readInit wire bytes = some packet ∧ RegistrationNativeKemTarget.PacketKey packet pair.1 := by
  have typed := raw_bundle_success setup checks wire route representation created credential selected pairs publicKey real parsed
    index bytes before after supported
  have compiled : (some (.ok (some bytes)), after) ∈ support
      (((simulateQ provider (simulateQ (lower false) (RegistrationNativeKemBeaconCompiler.beacon
        (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index)))).run).run before) := by
    simpa only [RegistrationNativeKemParsedRouting.handler, RegistrationNativeKemDispatcherCompiler.handler,
      lower, QueryImpl.simulateQ_compose] using typed
  obtain ⟨owner, packet, ownerAt, decoded, payload⟩ := RegistrationNativeKemOpenBeaconResult.bundle_key setup checks wire route representation
    created credential selected pairs publicKey real readback false index before after bytes compiled
  obtain ⟨pair, pairAt, _handle, key⟩ := prior.2 index owner ownerAt
  refine ⟨pair, packet, pairAt, ?_, decoded, ?_⟩
  · rw [prior.1]
    exact (List.getElem?_eq_some_iff.mp ownerAt).1
  · simpa only [key] using payload

end BeaconcryptCore.Computational.RegistrationNativeKemOpenPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPublication.bundle_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPublication.bundle_key
