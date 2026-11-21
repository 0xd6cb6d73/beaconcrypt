-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! Ordinary concrete native operations retain the entire private birth pool and owner capabilities. This isolates the actual Server/record source wrappers used by the initialized owner-to-generated-KEM-handle invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStatePreservation
open RegistrationNativeExperiment (State)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeWire (Wire)
attribute [local irreducible] RegistrationServerSdkSource.accept
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}

def SameOwners (before after : State n KemSK mlSource) : Prop :=
  after.pool = before.pool ∧ after.beacons = before.beacons

/-- Any reached actual Server subprogram retains the complete private pool and every Beacon capability. -/
theorem server_keeps (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.server work).run before)) : SameOwners before result.2 := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at reached
  obtain ⟨inner, _, rfl⟩ := reached
  exact ⟨rfl, rfl⟩

/-- Every actual record World effect leaves private registration ownership untouched. -/
theorem world_keeps (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.world work).run before)) : SameOwners before result.2 :=
  server_keeps _ before result reached

/-- Dynamic public owner-to-World routing preserves both the complete source owner list and indexed private KEM service. -/
theorem record_keeps (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK mlSource)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.record setup wire route query mlSource).run before)) :
    SameOwners before result.2 := by
  cases query with
  | inl query => exact world_keeps _ before result reached
  | inr query =>
    rcases query with ⟨owner, query⟩
    cases query <;> cases found : before.beacons[owner]? with
    | none =>
        simp only [RegistrationNativeExperiment.record, StateT.run, found, mem_support_pure_iff] at reached
        subst result
        exact ⟨rfl, rfl⟩
    | some selected =>
        simp only [RegistrationNativeExperiment.record, StateT.run, found] at reached
        exact world_keeps _ before result reached

def Ordinary : TypedSpec.Domain → Prop
  | .inr (.create _ _ _) | .inr (.bundle _) | .inr (.finish _ _) => False
  | _ => True

set_option maxRecDepth 4096 in
/-- The concrete source dispatch mutates birth ownership only through the three actual Beacon lifecycle operations. -/
theorem handler_keeps (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) (ordinary : Ordinary query) (before : State n KemSK mlSource)
    (result : TypedSpec.Range query × State n KemSK mlSource)
    (reached : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run before)) :
    SameOwners before result.2 := by
  cases query with
  | inl coin => exact world_keeps _ before result reached
  | inr query => cases query with
    | create edPin mlPin keyId => exact False.elim ordinary
    | bundle owner => exact False.elim ordinary
    | finish owner packet => exact False.elim ordinary
    | accept packet =>
        change result ∈ support ((RegistrationNativeExperiment.server
          (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify
            representation created packet)).run { before with parsedAccepts := before.parsedAccepts + 1 }) at reached
        have actual := server_keeps _ { before with parsedAccepts := before.parsedAccepts + 1 } result reached
        exact actual
    | build handle application => exact server_keeps _ before result reached
    | hmac key message =>
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, mem_support_pure_iff] at reached
        subst result
        exact ⟨rfl, rfl⟩
    | hash bytes => exact world_keeps _ before result reached
    | serverSend keyId plaintext => exact record_keeps setup wire route (.inl (.inl (plaintext, keyId))) before result reached
    | serverRaw raw => exact record_keeps setup wire route (.inl (.inr raw)) before result reached
    | beaconSend owner plaintext => exact record_keeps setup wire route (.inr (owner, .inl plaintext)) before result reached
    | beaconRaw owner raw => exact record_keeps setup wire route (.inr (owner, .inr raw)) before result reached

end BeaconcryptCore.Computational.RegistrationNativeStatePreservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStatePreservation.server_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStatePreservation.server_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStatePreservation.world_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStatePreservation.world_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStatePreservation.record_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStatePreservation.record_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStatePreservation.handler_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStatePreservation.handler_keeps
