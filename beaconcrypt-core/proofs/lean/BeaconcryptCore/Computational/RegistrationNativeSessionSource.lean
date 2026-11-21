-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape
import BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame

/-! Actual Native callbacks preserve the Server session roster except for successful acceptance. Build consumes slots without shortening the list; every failure and primitive poststate remains part of the same source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeSessionSource
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build

theorem world_sessions (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.world work).run before)) :
    result.2.server.sessions = before.server.sessions := by
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    StateT.run, Functor.map_map, support_map] at reached
  obtain ⟨inner, _, rfl⟩ := reached
  rfl

private theorem trusted_sessions (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : State n KemSK mlSource)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run before)) :
    result.2.server.sessions = before.server.sessions := by
  cases query with
  | inl query => exact world_sessions _ before result reached
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted, StateT.run, mem_support_bind_iff,
        mem_support_pure_iff] at reached
      obtain ⟨inner, _supported, equal⟩ := reached
      cases equal
      rfl

private theorem trusted_program_sessions (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) work).run before)) :
    result.2.server.sessions = before.server.sessions := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, tail⟩ := reached
      exact (ih middle.1 middle.2 result tail).trans
        (trusted_sessions setup checks representation created query before middle first)

/-- Every actual Beacon lifecycle AST retains Server sessions, including error continuations and indexed KEM effects. -/
theorem beacon_sessions (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    result.2.server.sessions = before.server.sessions := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    mem_support_pure_iff] at reached
  obtain ⟨inner, supported, equal⟩ := reached
  cases equal
  exact trusted_program_sessions setup checks representation created _ before inner supported

private theorem record_sessions (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK mlSource)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK mlSource)
    (reached : result ∈ support ((RegistrationNativeExperiment.record setup wire route query mlSource).run before)) :
    result.2.server.sessions = before.server.sessions := by
  cases query with
  | inl query => exact world_sessions _ before result reached
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query <;> cases found : before.beacons[owner]? with
      | none =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found, mem_support_pure_iff] at reached
          subst result
          rfl
      | some selected =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found] at reached
          exact world_sessions _ before result reached

def NonAccept : TypedSpec.Domain → Prop
  | .inr (.accept _) => False
  | _ => True

attribute [local irreducible] RegistrationNativeExperiment.beacon RegistrationNativeExperiment.record

/-- Every actual callback except acceptance retains the session roster length, including consumed build handles. -/
theorem typed_other (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) (nonAccept : NonAccept query)
    (before : State n KemSK mlSource) (result : TypedSpec.Range query × State n KemSK mlSource)
    (reached : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run before)) :
    result.2.server.sessions.length = before.server.sessions.length := by
  cases query with
  | inl coin => exact congrArg List.length (world_sessions _ before result reached)
  | inr command => cases command with
    | create edPin mlPin keyId => exact congrArg List.length (beacon_sessions setup checks representation created _ before result reached)
    | bundle owner => exact congrArg List.length (beacon_sessions setup checks representation created _ before result reached)
    | finish owner packet => exact congrArg List.length (beacon_sessions setup checks representation created _ before result reached)
    | accept packet => cases nonAccept
    | build handle application =>
        simp only [RegistrationNativeExperiment.handler, RegistrationNativeExperiment.server,
          StateT.run, support_map] at reached
        obtain ⟨inner, called, rfl⟩ := reached
        exact RegistrationNativeBuildSessionFrame.build setup (RegistrationNativeWire.ledgerCodec wire) checks
          (RegistrationNativeMldsa.owned mlSource credential) wire.encodeResponse handle application
          before.server inner.2 inner.1 called
    | hmac key message =>
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, mem_support_pure_iff] at reached
        subst result
        rfl
    | hash bytes => exact congrArg List.length (world_sessions _ before result reached)
    | serverSend keyId plaintext => exact congrArg List.length (record_sessions setup wire route (.inl (.inl (plaintext, keyId))) before result reached)
    | serverRaw raw => exact congrArg List.length (record_sessions setup wire route (.inl (.inr raw)) before result reached)
    | beaconSend owner plaintext => exact congrArg List.length (record_sessions setup wire route (.inr (owner, .inl plaintext)) before result reached)
    | beaconRaw owner raw => exact congrArg List.length (record_sessions setup wire route (.inr (owner, .inr raw)) before result reached)

/-- The actual parsed-attempt charge does not alter the successful SDK append position or any session roster outcome. -/
theorem typed_accept (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (packet : beaconcrypt_core.registration.InitPacket)
    (before after : State n KemSK mlSource) (reply : RustM (Option Nat)) :
    (reply, after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential (.inr (.accept packet))).run before) →
    RegistrationNativeAcceptSessionShape.Shape before.server.sessions reply after.server.sessions := by
  change (reply, after) ∈ support ((RegistrationNativeExperiment.server
    (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify
      representation created packet)).run { before with parsedAccepts := before.parsedAccepts + 1 }) → _
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map]
  rintro ⟨inner, _, same⟩
  cases same
  exact RegistrationNativeAcceptSessionShape.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify
    representation created packet before.server inner.2 inner.1 (by assumption)

end BeaconcryptCore.Computational.RegistrationNativeSessionSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionSource.world_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionSource.world_sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionSource.beacon_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionSource.beacon_sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionSource.typed_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionSource.typed_other

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionSource.typed_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionSource.typed_accept
