-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform

/-! Ordinary native response construction and records are pool-free ambient operations. Birth/decapsulation stay behind the indexed private service and the actual selected Server encapsulation getter remains exposed. The executable client has no selected KEM secret. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFrontendInterface
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (RecordQuery RecordSpec)
open RegistrationNativeKemServerState (State mask)
open RegistrationNativeWire (Wire ledgerCodec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

inductive Ordinary where
  | build (session : Nat) (application : Option (Slice U8))
  | record (query : RecordQuery)

abbrev OrdinarySpec : OracleSpec Ordinary
  | .build _ _ => RustM (Option (U64 × Pqxdh.Bytes))
  | .record query => (RecordSpec .O).Range query

abbrev Ambient (n : Nat) (mlSource : RegistrationNativeMldsa.Source) :=
  RegistrationNativeKemServerInterface.Ambient n mlSource + OrdinarySpec

abbrev Spec (n : Nat) (mlSource : RegistrationNativeMldsa.Source) (KemSK : Type) :=
  RegistrationNativeKemInterface.Spec (Ambient n mlSource) KemSK

def lift : QueryImpl (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
    (OracleComp (Spec n mlSource KemSK))
  | .inl query => (Spec n mlSource KemSK).query (.inl (.inl query))
  | .inr (.inl query) => (Spec n mlSource KemSK).query (.inr (.inl query))
  | .inr (.inr key) => (Spec n mlSource KemSK).query (.inr (.inr key))

def world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) : StateT (State n mlSource) ProbComp Value :=
  fun before => (fun result => (result.1, mask { before with server := { before.server with world :=
    { before.server.world with world := (result.2, before.server.world.world.2) } } })) <$> work.run before.server.world.world.1

/-- Public owner indices resolve the actual retained World owner; no index equality is assumed. -/
noncomputable def record (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (RecordSpec .O) (StateT (State n mlSource) ProbComp)
  | .inl query => world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route (.inr (.inr (.inl query))))
  | .inr (owner, .inl plaintext) => fun before => match before.beacons[owner]? with
      | none => pure (none, mask before)
      | some selected => (world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))).run before
  | .inr (owner, .inr raw) => fun before => match before.beacons[owner]? with
      | none => pure (.None, mask before)
      | some selected => (world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))).run before

noncomputable def other (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl (Ambient n mlSource) (StateT (State n mlSource) ProbComp)
  | .inl query => RegistrationNativeKemServerInterface.other setup (ledgerCodec wire) checks route mlSource.verify representation created query
  | .inr (.build session application) => RegistrationNativeKemServerInterface.server
      (RegistrationServerSdkSource.build setup (ledgerCodec wire) checks
        (RegistrationNativeMldsa.owned mlSource credential) wire.encodeResponse session application)
  | .inr (.record query) => record setup wire route query

noncomputable def source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl (Spec n mlSource KemSK) (StateT (State n mlSource × PqxdhLiveKemBirth.Pool KemSK) ProbComp) :=
  RegistrationNativeKemInterface.source setup.baseImpl setup.kem (Ambient n mlSource)
    (other setup checks wire route representation created credential)

/-- Adding ordinary pool-free operations preserves the complete existing selected-KEM client interpretation. -/
theorem lift_program (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) Value)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup checks wire route representation created credential) (simulateQ lift work)).run before =
      (simulateQ (RegistrationNativeKemServerInterface.source setup (ledgerCodec wire) checks route mlSource.verify representation created) work).run before := by
  have step : (source (n := n) setup checks wire route representation created credential) ∘ₛ lift =
      RegistrationNativeKemServerInterface.source setup (ledgerCodec wire) checks route mlSource.verify representation created := by
    funext query
    rcases query with query | (query | key) <;>
      simp only [QueryImpl.compose, lift, simulateQ_spec_query, source, other,
        RegistrationNativeKemInterface.source, RegistrationNativeKemServerInterface.source]
    cases query <;> rfl
  rw [← QueryImpl.simulateQ_compose, step]

end BeaconcryptCore.Computational.RegistrationNativeKemFrontendInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFrontendInterface.lift_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFrontendInterface.lift_program
