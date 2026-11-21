-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! The private source parsed-call counter advances exactly once at typed accept entry. Actual World effects, indexed KEM operations, local Beacon controllers, records and failed publications retain it. No session, owner or private KEM handle is identified with this counter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build

/-- Arbitrary actual Server subprograms leave the independently stored parsed-attempt counter intact. -/
theorem server_counter (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.server work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at reached
  obtain ⟨inner, _supported, rfl⟩ := reached
  rfl

private theorem world_counter (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.world work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := server_counter _ before result reached

private theorem trusted_counter (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : State n KemSK mlSource)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  cases query with
  | inl query => exact world_counter _ before result reached
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted, StateT.run, mem_support_bind_iff,
        mem_support_pure_iff] at reached
      obtain ⟨inner, _supported, equal⟩ := reached
      cases equal
      rfl

private theorem trusted_program_counter (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, tail⟩ := reached
      exact (ih middle.1 middle.2 result tail).trans
        (trusted_counter setup checks representation created query before middle first)

/-- Every actual Beacon lifecycle AST keeps the parsed-attempt counter, including all error continuations and private indexed KEM effects. -/
theorem beacon_counter (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    mem_support_pure_iff] at reached
  obtain ⟨inner, supported, equal⟩ := reached
  cases equal
  exact trusted_program_counter setup checks representation created _ before inner supported

private theorem record_counter (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK mlSource)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.record setup wire route query mlSource).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  cases query with
  | inl query => exact world_counter _ before result reached
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query <;> cases found : before.beacons[owner]? with
      | none =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found, mem_support_pure_iff] at reached
          subst result
          rfl
      | some selected =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found] at reached
          exact world_counter _ before result reached

def isAccept : TypedSpec.Domain → Bool
  | .inr (.accept _) => true
  | _ => false

attribute [local irreducible] RegistrationNativeExperiment.beacon RegistrationNativeExperiment.record

set_option maxRecDepth 2048 in
/-- The actual dispatcher increments before every decoded attempt, including failed authentication and replay. -/
theorem typed_counter (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) (before : State n KemSK mlSource)
    (result : TypedSpec.Range query × State n KemSK mlSource)
    (reached : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept query).toNat := by
  cases query with
  | inl coin => exact world_counter _ before result reached
  | inr command => cases command with
    | create edPin mlPin keyId => exact beacon_counter setup checks representation created _ before result reached
    | bundle owner => exact beacon_counter setup checks representation created _ before result reached
    | finish owner packet => exact beacon_counter setup checks representation created _ before result reached
    | accept packet =>
        change result ∈ support ((RegistrationNativeExperiment.server
          (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify
            representation created packet)).run { before with parsedAccepts := before.parsedAccepts + 1 }) at reached
        exact server_counter _ _ result reached
    | build handle application => exact server_counter _ before result reached
    | hmac key message =>
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, mem_support_pure_iff] at reached
        subst result
        rfl
    | hash bytes => exact world_counter _ before result reached
    | serverSend keyId plaintext => exact record_counter setup wire route (.inl (.inl (plaintext, keyId))) before result reached
    | serverRaw raw => exact record_counter setup wire route (.inl (.inr raw)) before result reached
    | beaconSend owner plaintext => exact record_counter setup wire route (.inr (owner, .inl plaintext)) before result reached
    | beaconRaw owner raw => exact record_counter setup wire route (.inr (owner, .inr raw)) before result reached

end BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource.server_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource.server_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource.beacon_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource.beacon_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource.typed_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedCounterSource.typed_counter
