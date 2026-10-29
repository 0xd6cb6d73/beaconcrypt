-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdHistorySource

/-! The fixed-prekey signing history holds for the actual adaptive native source dispatcher and the original raw CE ledger. Construction extends the generated-owner roster; outgoing attempts extend only their own history, while all other native operations preserve it. The result includes malformed finish consumption and every optional failure state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeEdHistory (Fixed)
open RegistrationNativeExperiment (State)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build

private theorem server_keeps {source : RegistrationNativeMldsa.Source}
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.server work).run before)) :
    result.2.beacons = before.beacons := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨inner, _, returned⟩ := supported
  cases returned
  rfl

private theorem world_keeps {source : RegistrationNativeMldsa.Source}
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.world work).run before)) :
    result.2.beacons = before.beacons := server_keeps _ _ _ supported

private theorem record_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.record setup wire route query source).run before)) :
    result.2.beacons = before.beacons := by
  cases query with
  | inl query => exact world_keeps _ _ _ supported
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query with
      | inl plaintext =>
          simp only [RegistrationNativeExperiment.record, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            cases supported
            rfl
          · exact world_keeps _ _ _ supported
      | inr raw =>
          simp only [RegistrationNativeExperiment.record, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            cases supported
            rfl
          · exact world_keeps _ _ _ supported

/-- Every actual typed operation preserves the derived generated-owner history invariant. -/
theorem handler_fixed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (prior : Fixed before.beacons)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    Fixed result.2.beacons := by
  cases query with
  | inl coin => exact (world_keeps _ _ _ supported).symm ▸ prior
  | inr command =>
      cases command with
      | create edPin mlPin keyId =>
          exact RegistrationNativeEdHistorySource.source_create_fixed setup checks representation created source edPin mlPin keyId before result prior supported
      | bundle owner =>
          exact RegistrationNativeEdHistorySource.source_bundle_fixed setup checks representation created source wire owner before result prior supported
      | finish owner packet =>
          exact RegistrationNativeEdHistorySource.source_finish_fixed setup checks representation created source wire owner packet before result prior supported
      | accept packet =>
          simp only [RegistrationNativeExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at supported
          exact (server_keeps _ _ _ supported).symm ▸ prior
      | build session application => exact (server_keeps _ _ _ supported).symm ▸ prior
      | hmac key message =>
          simp only [RegistrationNativeExperiment.handler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact prior
      | hash bytes => exact (world_keeps _ _ _ supported).symm ▸ prior
      | serverSend keyId plaintext => exact (record_keeps setup wire route source (.inl (.inl (plaintext, keyId))) before result supported).symm ▸ prior
      | serverRaw raw => exact (record_keeps setup wire route source (.inl (.inr raw)) before result supported).symm ▸ prior
      | beaconSend owner plaintext => exact (record_keeps setup wire route source (.inr (owner, .inl plaintext)) before result supported).symm ▸ prior
      | beaconRaw owner raw => exact (record_keeps setup wire route source (.inr (owner, .inr raw)) before result supported).symm ▸ prior

/-- Arbitrary adaptive clients retain the same invariant at every reached native prefix. -/
theorem program_fixed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK source)
    (result : Value × State n KemSK source) (prior : Fixed before.beacons)
    (supported : result ∈ support
      ((simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before)) :
    Fixed result.2.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (fun state => Fixed state.beacons)
    (fun query current valid result reached => handler_fixed setup checks wire route representation created source credential query current result valid reached)
    work before prior result supported

/-- The original secrecy ledger changes only public query flow and retains the actual native histories beneath it. -/
theorem run_fixed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source)) (prior : Fixed before.beacons)
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Fixed result.2.2.beacons := by
  rw [RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  exact program_fixed setup checks wire route representation created source credential _ before inner prior reached

/-- Actual native startup introduces an empty owner roster, independently of constructor or ML-generation failures. -/
theorem start_fixed (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Fixed initial.state.beacons := by
  unfold RegistrationNativeExperiment.start at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨constructed, _, continued⟩ := supported
  cases built : constructed.1.1 with
  | none => simp only [built, support_pure, Set.mem_singleton_iff] at continued; cases continued
  | some created =>
      rw [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _, continued⟩ := continued
      cases chosen : generated.1 with
      | none => simp only [chosen, support_pure, Set.mem_singleton_iff] at continued; cases continued
      | some credential =>
          rw [chosen, mem_support_bind_iff] at continued
          obtain ⟨initialized, _, continued⟩ := continued
          split at continued
          · simp only [support_pure, Set.mem_singleton_iff] at continued
            cases continued
            exact RegistrationNativeEdHistorySource.fixed_empty source
          · simp only [support_pure, Set.mem_singleton_iff] at continued
            cases continued

/-- Every reached original-CE prefix from actual source initialization has only the source owner's allowed signing messages. -/
theorem initialized_run_fixed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (born : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state)) :
    Fixed result.2.2.beacons :=
  run_fixed setup checks wire route representation initial.created source initial.credential bounds mode work initial.state result
    (start_fixed setup source ensureInit identityIndex serverKeyId initial born) supported

end BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.handler_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.handler_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.program_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.program_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.run_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.run_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.start_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.start_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.initialized_run_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun.initialized_run_fixed
