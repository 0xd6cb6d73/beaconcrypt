-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace
import BeaconcryptCore.Computational.RegistrationNativeScalarRoster

/-! The actual immutable owner-pin list changes only at successful construction. Every other typed or secrecy-generated raw program retains that list, derived from its actual no-create query tree and the existing whole-owner metadata receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}

def pins (owners : RegistrationNativeBeaconFrontend.State source) : List (PqxdhBeaconPhase2Preparation.Word32 × U64) :=
  owners.map fun owner => (owner.pin.binding.identity_public_key, owner.pin.binding.identity_key_id)

/-- Current owner pins are unchanged by any non-create native typed callback. -/
theorem noncreate_pins (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (query : TypedSpec.Domain) (notCreate : ∀ edPin mlPin keyId, query ≠ .inr (.create edPin mlPin keyId))
    (before : State n KemSK source) (result : TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    pins result.2.beacons = pins before.beacons := by
  obtain ⟨tail, same⟩ := RegistrationNativeOwnerRoster.typed_prefix setup checks wire route representation created credential query before result supported
  have lengthEq := RegistrationNativeScalarRoster.noncreate_length setup checks wire route representation created credential query notCreate before result supported
  have sizes := congrArg List.length same
  simp only [List.length_map, List.length_append, lengthEq] at sizes
  have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
  rw [empty, List.append_nil] at same
  have pinned := congrArg (fun owners => pins owners) same
  simpa only [pins, List.map_map, RegistrationNativeOwnerFields.metadata, Function.comp_def] using pinned

/-- Entire typed programs with no constructor query preserve every configured owner binding. -/
theorem typed_quiet (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp TypedSpec Value)
    (quiet : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) 0)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before)) :
    pins result.2.beacons = pins before.beacons := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have absent : RegistrationNativeRawAdapter.kind query ≠ 1 := quiet.1.resolve_right (Nat.not_lt_zero _)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have first := noncreate_pins setup checks wire route representation created credential query
        (fun edPin mlPin keyId same => absent (by cases same; rfl)) before middle reached
      exact (ih middle.1 (by simpa using quiet.2 middle.1) middle.2 result continued).trans first

/-- Raw adapter parsing and reply projection do not add constructors to a no-create program. -/
theorem raw_quiet (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeInterface.Spec Value)
    (quiet : work.IsQueryBoundP (fun query => RegistrationNativeLedgerCaps.coreKind query = 1) 0)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential) work).run before)) :
    pins result.2.beacons = pins before.beacons := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact typed_quiet setup checks wire route representation created credential _
    (RegistrationNativeRawAdapter.compile_bound wire work 1 0 quiet) before result supported

/-- The original hidden-bit/fresh-message query tree contains no owner constructor, even before its cursor or native admission. -/
theorem secrecy_quiet (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (before : RegistrationNativeLedger.State) :
    ((RegistrationNativeLedger.handler crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds (.inr secrecy)).run before).IsQueryBoundP
      (fun query => RegistrationNativeLedgerCaps.coreKind query = 1) 0 := by
  have actual := RegistrationNativeLedgerCaps.step_bound crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds 1 (.inr secrecy) before
  cases secrecy <;> simpa [PqxdhDeploymentCompileSecrecy.wrapCost, RegistrationNativeInterface.queryClass,
    RegistrationNativeInterface.eraseQuery, PqxdhDeploymentInterface.queryClass] using actual

end BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.noncreate_pins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.noncreate_pins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.typed_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.typed_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.raw_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.raw_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.secrecy_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore.secrecy_quiet
