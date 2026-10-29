-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory

/-! Every actual typed native operation retains genuine generated ownership, distinct handles and exact per-handle signing-history synchronization, including public reports and every native failure path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (interpret)
open RegistrationNativeIdentityMainHistory (Inv)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build

/-- Pure API replies retain every generated owner and its private indexed seed. -/
theorem pure_inv (joint : PqxdhJointIdentity.Primitives) (value : Value)
    (before : State n KemSK mlSource × SourceState) (result : Value × (State n KemSK mlSource × SourceState))
    (owned : Inv joint before) (reached : result ∈ support ((interpret joint (pure value)).run before)) :
    Inv joint result.2 := by
  rw [RegistrationNativeIdentityMainOrdinary.interpret_pure] at reached
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
  cases reached
  exact owned

private theorem server_inv (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (before : State n KemSK mlSource × SourceState) (result : Value × (State n KemSK mlSource × SourceState))
    (owned : Inv joint before)
    (reached : result ∈ support ((interpret joint (RegistrationNativeIdentityMain.server work)).run before)) :
    Inv joint result.2 :=
  RegistrationNativeIdentityMainHistory.ordinary_inv joint _ before result owned reached

private theorem world_inv (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK mlSource × SourceState) (result : Value × (State n KemSK mlSource × SourceState))
    (owned : Inv joint before)
    (reached : result ∈ support ((interpret joint (RegistrationNativeIdentityMain.world work)).run before)) :
    Inv joint result.2 := server_inv joint _ before result owned reached

/-- Actual record lookup and all actual record outcomes preserve private indexed ownership. -/
theorem record_inv (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State n KemSK mlSource × SourceState)
    (result : ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) × (State n KemSK mlSource × SourceState))
    (owned : Inv setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.record setup wire route query)).run before)) :
    Inv setup.joint result.2 := by
  cases query with
  | inl query => exact world_inv setup.joint _ before result owned reached
  | inr query =>
      rcases query with ⟨index, query⟩
      cases query with
      | inl plaintext =>
          unfold RegistrationNativeIdentityMain.record at reached
          rw [RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
            RegistrationNativeIdentityMainState.get_source, pure_bind] at reached
          cases found : before.1.beacons[index]? with
          | none =>
              simp only [found] at reached
              exact pure_inv setup.joint _ before result owned reached
          | some selected =>
              simp only [found] at reached
              exact world_inv setup.joint _ before result owned reached
      | inr raw =>
          unfold RegistrationNativeIdentityMain.record at reached
          rw [RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
            RegistrationNativeIdentityMainState.get_source, pure_bind] at reached
          cases found : before.1.beacons[index]? with
          | none =>
              simp only [found] at reached
              exact pure_inv setup.joint _ before result owned reached
          | some selected =>
              simp only [found] at reached
              exact world_inv setup.joint _ before result owned reached

/-- Reporting aliases, incrementing the actual parsed counter and native Server acceptance retain all genuine generated credentials. -/
theorem accept_inv (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket) (before : State n KemSK mlSource × SourceState)
    (result : RustM (Option Nat) × (State n KemSK mlSource × SourceState)) (owned : Inv setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential
      (.inr (.accept packet)))).run before)) : Inv setup.joint result.2 := by
  unfold RegistrationNativeIdentityMain.handler at reached
  rw [RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
    RegistrationNativeIdentityMainOrdinary.report_source, pure_bind,
    RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
    RegistrationNativeIdentityMainState.modify_source, pure_bind] at reached
  exact server_inv setup.joint
    (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify representation created packet)
    ({ before.1 with context := { before.1.context with parsedAccepts := before.1.context.parsedAccepts + 1 } }, before.2)
    result owned reached

/-- Every actual typed native operation preserves the internal source ownership invariant without any public-event restriction. -/
theorem handler_inv (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK mlSource × SourceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × (State n KemSK mlSource × SourceState))
    (owned : Inv setup.joint before)
    (reached : result ∈ support ((interpret setup.joint
      (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential query)).run before)) :
    Inv setup.joint result.2 := by
  cases query with
  | inl coin => exact world_inv setup.joint _ before result owned reached
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativeIdentityMainHistory.create_inv setup checks representation created edPin mlPin keyId before result owned reached
    | bundle owner => exact RegistrationNativeIdentityMainHistory.bundle_inv setup checks representation created wire owner before result owned reached
    | accept packet => exact accept_inv setup checks wire route representation created credential packet before result owned reached
    | build session application => exact server_inv setup.joint _ before result owned reached
    | finish owner packet => exact RegistrationNativeIdentityMainHistory.finish_inv setup checks representation created wire owner packet before result owned reached
    | hmac key message => exact pure_inv setup.joint _ before result owned reached
    | hash bytes => exact world_inv setup.joint _ before result owned reached
    | serverSend keyId plaintext => exact record_inv setup wire route (.inl (.inl (plaintext, keyId))) before result owned reached
    | serverRaw raw => exact record_inv setup wire route (.inl (.inr raw)) before result owned reached
    | beaconSend owner plaintext => exact record_inv setup wire route (.inr (owner, .inl plaintext)) before result owned reached
    | beaconRaw owner raw => exact record_inv setup wire route (.inr (owner, .inr raw)) before result owned reached

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.pure_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.pure_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.record_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.record_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.accept_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.accept_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.handler_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped.handler_inv
