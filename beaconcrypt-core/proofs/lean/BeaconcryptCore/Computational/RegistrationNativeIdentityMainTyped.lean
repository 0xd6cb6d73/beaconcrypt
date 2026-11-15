-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainRecord
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle

/-! Every typed operation of the ordinary joint-service native client recovers the original native Main operation. Actual prefix reports are ghost source observations; mandatory authentication, replay, reservation, native KEM, moved handles and full failure state remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (interpret project Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Current-prefix alias reports precede the actual parsed-attempt increment and native SDK acceptance without changing any source field. -/
theorem accept_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket) (before : State n KemSK mlSource × SourceState) :
    Prod.map id project <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential
        (.inr (.accept packet)))).run before =
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential
        (.inr (.accept packet))).run (project before) := by
  unfold RegistrationNativeIdentityMain.handler
  rw [RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
    RegistrationNativeIdentityMainOrdinary.report_source, pure_bind,
    RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
    RegistrationNativeIdentityMainState.modify_source, pure_bind]
  have law := RegistrationNativeIdentityMainState.server_source setup.joint
    (RegistrationServerSdkSource.accept setup (ledgerCodec wire) checks route mlSource.verify representation created packet)
    ({ before.1 with context := { before.1.context with parsedAccepts := before.1.context.parsedAccepts + 1 } }, before.2)
  simp only [RegistrationNativeExperiment.handler, StateT.run_bind, StateT.run_modify,
    pure_bind, project] at law ⊢
  exact law

/-- All actual typed source requests recover the complete original native operation from internally owned generated credentials. -/
theorem handler_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK mlSource × SourceState)
    (owned : Owned setup.joint before) :
    Prod.map id project <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential query)).run before =
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run (project before) := by
  cases query with
  | inl coin => exact RegistrationNativeIdentityMainState.world_source setup.joint _ before
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativeIdentityMainLifecycle.create_source setup checks representation created edPin mlPin keyId before owned
    | bundle owner => exact RegistrationNativeIdentityMainLifecycle.bundle_source setup checks representation created wire owner before owned
    | accept packet => exact accept_source setup checks wire route representation created credential packet before
    | build session application => exact RegistrationNativeIdentityMainState.server_source setup.joint _ before
    | finish owner packet => exact RegistrationNativeIdentityMainLifecycle.finish_source setup checks representation created wire owner packet before owned
    | hmac key message => exact RegistrationNativeIdentityMainState.pure_source setup.joint _ before
    | hash bytes => exact RegistrationNativeIdentityMainState.world_source setup.joint _ before
    | serverSend keyId plaintext => exact RegistrationNativeIdentityMainRecord.record_source setup wire route (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact RegistrationNativeIdentityMainRecord.record_source setup wire route (.inl (.inr raw)) before
    | beaconSend owner plaintext => exact RegistrationNativeIdentityMainRecord.record_source setup wire route (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw => exact RegistrationNativeIdentityMainRecord.record_source setup wire route (.inr (owner, .inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainTyped.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainTyped.accept_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainTyped.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainTyped.handler_source
