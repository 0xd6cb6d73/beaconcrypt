-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCapsCore
import BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCompilerCaps

/-! Each actual typed native command creates at most one indexed Ed identity exactly in its create branch. The complete stateful native compiler therefore transports the ordinary original-command create cap to the joint-service client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State M)
open RegistrationNativeIdentityMainCreateCapsCore
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build

private theorem server_zero (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) :
    Bound (RegistrationNativeIdentityMain.server work : M n KemSK source Value) 0 := ordinary_zero _

private theorem world_zero (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    Bound (RegistrationNativeIdentityMain.world work : M n KemSK source Value) 0 := server_zero _

theorem record_zero (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) :
    Bound (RegistrationNativeIdentityMain.record setup wire route query : M n KemSK source _) 0 := by
  cases query with
  | inl query => exact world_zero _
  | inr query =>
      rcases query with ⟨index, query⟩
      cases query with
      | inl plaintext =>
          unfold RegistrationNativeIdentityMain.record
          apply bind_bound _ _ 0 0 get_zero
          intro before
          cases before.beacons[index]? with
          | none => exact pure_zero _
          | some selected => exact world_zero _
      | inr raw =>
          unfold RegistrationNativeIdentityMain.record
          apply bind_bound _ _ 0 0 get_zero
          intro before
          cases before.beacons[index]? with
          | none => exact pure_zero _
          | some selected => exact world_zero _

theorem accept_zero (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (packet : beaconcrypt_core.registration.InitPacket) :
    Bound (RegistrationNativeIdentityMain.handler (n := n) setup checks wire route representation created credential (.inr (.accept packet))) 0 := by
  unfold RegistrationNativeIdentityMain.handler
  exact bind_bound _ _ 0 0 (report_zero packet) (fun _ =>
    bind_bound _ _ 0 0 (modify_zero _) (fun _ => server_zero _))

/-- Actual native owner creation is the only typed branch charged by the ordinary indexed identity-create class. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Bound (RegistrationNativeIdentityMain.handler (n := n) setup checks wire route representation created credential query)
      (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin => exact world_zero _
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact RegistrationNativeIdentityCreateCompilerCaps.beacon_bound setup checks representation created _ 1
          (RegistrationNativeIdentityCreateCaps.create_one setup edPin mlPin keyId)
    | bundle owner =>
        exact RegistrationNativeIdentityCreateCompilerCaps.beacon_bound setup checks representation created _ 0
          (RegistrationNativeIdentityNoCreate.bundle_zero setup wire owner)
    | accept packet => exact accept_zero setup checks wire route representation created credential packet
    | build session application => exact server_zero _
    | finish owner packet =>
        exact RegistrationNativeIdentityCreateCompilerCaps.beacon_bound setup checks representation created _ 0
          (RegistrationNativeIdentityNoCreate.finish_zero setup wire owner packet)
    | hmac key message => exact pure_zero _
    | hash bytes => exact world_zero _
    | serverSend keyId plaintext => exact record_zero setup wire route (.inl (.inl (plaintext, keyId)))
    | serverRaw raw => exact record_zero setup wire route (.inl (.inr raw))
    | beaconSend owner plaintext => exact record_zero setup wire route (.inr (owner, .inl plaintext))
    | beaconRaw owner raw => exact record_zero setup wire route (.inr (owner, .inr raw))

/-- A whole typed-adversary create cap bounds the ordinary joint client's identity creations on all replies, including non-winning continuations. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap)
    (before : State n KemSK source) :
    ((simulateQ (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential) work).run before).IsQueryBoundP
      Creates cap :=
  OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded
    (fun query current => handler_bound setup checks wire route representation created credential query current) before

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.record_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.record_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.accept_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps.program_bound
