-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerPinFields
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterLedger

/-! All actual native commands preserve the configured Server authentication pin. Beacon callbacks may update the shared World and chronological receipts, and original secrecy commands may add hidden draws, but none changes this pin. The invariant applies to arbitrary complete original-ledger native programs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPinTrace
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build

theorem world_pin (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.world work).run before)) : result.2.server.pin = before.server.pin := by
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run,
    Functor.map_map, support_map] at supported
  obtain ⟨current, _reached, rfl⟩ := supported
  rfl

theorem trusted_pin (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : State n KemSK source) (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    result.2.server.pin = before.server.pin := by
  cases query with
  | inl effect => exact world_pin _ before result supported
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨current, _reached, returned⟩ := supported
      cases returned
      rfl

theorem trusted_program_pin (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    result.2.server.pin = before.server.pin := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeExperiment.trusted setup checks representation created source)
    (fun current => current.server.pin = before.server.pin)
    (fun query current prior next reached => (trusted_pin setup checks representation created query current next reached).trans prior)
    work before rfl result supported

theorem beacon_pin (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    result.2.server.pin = before.server.pin := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨current, reached, returned⟩ := supported
  have pin := trusted_program_pin setup checks representation created _ before current reached
  cases returned
  exact pin

private theorem server_pin (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (keeps : ∀ before result, result ∈ support (work.run before) → result.2.pin = before.pin)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.server work).run before)) : result.2.server.pin = before.server.pin := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨current, reached, rfl⟩ := supported
  exact keeps before.server current reached

private theorem record_pin (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State n KemSK source) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.record setup wire route query source).run before)) :
    result.2.server.pin = before.server.pin := by
  cases query with
  | inl query => exact world_pin _ before result supported
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query <;> cases found : before.beacons[owner]? with
      | none => simp only [RegistrationNativeExperiment.record, StateT.run, found, mem_support_pure_iff] at supported; cases supported; rfl
      | some selected =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found] at supported
          exact world_pin _ before result supported

/-- Every actual typed command retains the same pin, including source accept/build and arbitrary Beacon operations. -/
theorem handler_pin (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : TypedSpec.Domain) (before : State n KemSK source) (result : TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    result.2.server.pin = before.server.pin := by
  cases query with
  | inl coin => exact world_pin _ before result supported
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon_pin setup checks representation created _ before result supported
    | bundle owner => exact beacon_pin setup checks representation created _ before result supported
    | finish owner packet => exact beacon_pin setup checks representation created _ before result supported
    | accept packet =>
        change result ∈ support ((RegistrationNativeExperiment.server
          (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
            representation created packet)).run { before with parsedAccepts := before.parsedAccepts + 1 }) at supported
        exact server_pin _ (RegistrationNativeServerPinFields.accept_pin setup (RegistrationNativeWire.ledgerCodec wire)
          checks route source.verify representation created packet) { before with parsedAccepts := before.parsedAccepts + 1 } result supported
    | build handle application =>
        exact server_pin _ (RegistrationNativeServerPinFields.build_pin setup (RegistrationNativeWire.ledgerCodec wire) checks
          (RegistrationNativeMldsa.owned source credential) wire.encodeResponse handle application) before result supported
    | hmac key message => simp only [RegistrationNativeExperiment.handler, StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl
    | hash bytes => exact world_pin _ before result supported
    | serverSend keyId plaintext => exact record_pin setup wire route (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record_pin setup wire route (.inl (.inr raw)) before result supported
    | beaconSend owner plaintext => exact record_pin setup wire route (.inr (owner, .inl plaintext)) before result supported
    | beaconRaw owner raw => exact record_pin setup wire route (.inr (owner, .inr raw)) before result supported

theorem program_pin (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp TypedSpec Value) (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before)) :
    result.2.server.pin = before.server.pin := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
    (fun current => current.server.pin = before.server.pin)
    (fun query current prior next reached => (handler_pin setup checks wire route representation created credential query current next reached).trans prior)
    work before rfl result supported

private theorem raw_program_pin (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeInterface.Spec Value) (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)) work).run before)) :
    result.2.server.pin = before.server.pin := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_pin setup checks wire route representation created credential _ before result supported

/-- The complete original ledger step retains the pin through hidden secrecy draws and internal record sends. -/
theorem full_step_pin (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    result.2.2.server.pin = before.2.server.pin := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨current, reached, rfl⟩ := supported
  exact raw_program_pin setup checks wire route representation created credential _ before.2 current reached

/-- Arbitrary original native runs retain the actual initial Server authentication pin in their complete poststate. -/
theorem run_pin (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    result.2.2.server.pin = before.server.pin := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential))
    (fun current => current.2.server.pin = before.server.pin)
    (fun query current prior next reached => (full_step_pin setup checks wire route representation created credential bounds query current next reached).trans prior)
    _ (RegistrationNativeLedger.empty, before) rfl result supported

end BeaconcryptCore.Computational.RegistrationNativeServerPinTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.world_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.world_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.trusted_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.trusted_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.trusted_program_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.trusted_program_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.beacon_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.beacon_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.handler_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.handler_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.program_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.program_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.full_step_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.full_step_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.run_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinTrace.run_pin
