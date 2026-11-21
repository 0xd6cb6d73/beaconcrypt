-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/-! The whole native typed client retains public indexed Beacon credentials while sending their signing and static-DH operations to the ordinary joint service. Independent Server, ML and KEM state stays local. Every parsed accept reports all current generated public-key aliases at its actual prefix. Reports are ghost operations in the source interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMain
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeIdentityWorld (Context)
open PqxdhJointPhase1Reports (ProtocolSpec CandidateReport)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

structure State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) where
  context : Context n KemSK
  beacons : RegistrationNativeIdentityFrontend.State source

abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (State n KemSK source) (OracleComp ProtocolSpec)

def dynamicLift : QueryImpl PqxdhDynamicIdentityPool.DynamicSpec (OracleComp ProtocolSpec) :=
  fun query => ProtocolSpec.query (.inl query)

def coins : QueryImpl unifSpec (OracleComp ProtocolSpec) :=
  fun query => ProtocolSpec.query (.inl (.inl query))

/-- Ordinary native work has already charged its own World counters; only its underlying random queries are forwarded here. -/
def ordinary (work : StateT (Context n KemSK) ProbComp Value) : M n KemSK mlSource Value := fun before =>
  (fun result => (result.1, { before with context := result.2 })) <$> simulateQ coins (work.run before.context)

def server (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) : M n KemSK mlSource Value :=
  ordinary fun before => (fun result => (result.1, { before with server := result.2 })) <$> work.run before.server

def world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) : M n KemSK mlSource Value :=
  server fun before => (fun result => (result.1,
    { before with world := { before.world with world := (result.2, before.world.world.2) } })) <$>
      work.run before.world.world.1

noncomputable def beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State mlSource Value) :
    M n KemSK mlSource Value := fun before => do
  let result ← simulateQ dynamicLift
    ((simulateQ (RegistrationNativeIdentityCompiler.implementation (source := mlSource) setup checks representation created)
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.context.server.world))).run before.context)
  pure (result.1.1.1, {
    context := { result.2 with
      server := { result.2.server with
        world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } }
    beacons := result.1.1.2 })

def reports (packet : registration.InitPacket) (owners : RegistrationNativeIdentityFrontend.State mlSource) : List CandidateReport :=
  owners.filterMap fun owner =>
    if PqxdhEd25519EufCma.encodedIdentity owner.identity.publicIdentity.ed25519 = PqxdhRefinement.absBytes packet.identity_key then
      some ⟨owner.identity.handle, RegistrationRootInput.candidate packet⟩
    else none

def emit : List CandidateReport → OracleComp ProtocolSpec Unit
  | [] => pure ()
  | report :: rest => do
      let _ ← ProtocolSpec.query (.inr report)
      emit rest

def report (packet : registration.InitPacket) : M n KemSK mlSource Unit := do
  let before ← get
  StateT.lift (emit (reports packet before.beacons))

noncomputable def record (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) :
    M n KemSK mlSource ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) :=
  match query with
  | .inl query => world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route (.inr (.inr (.inl query))))
  | .inr (index, .inl plaintext) => do
      let before ← get
      match before.beacons[index]? with
      | none => pure none
      | some selected => world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))
  | .inr (index, .inr raw) => do
      let before ← get
      match before.beacons[index]? with
      | none => pure .None
      | some selected => world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (M n KemSK mlSource)
  | .inl coin => world (PqxdhRecordLiftWorld.effects (.inl coin))
  | .inr (.create edPin mlPin keyId) => beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.create setup mlSource edPin mlPin keyId)
  | .inr (.bundle owner) => beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.bundle setup mlSource wire owner)
  | .inr (.accept packet) => do
      report packet
      modify fun before => { before with context := { before.context with parsedAccepts := before.context.parsedAccepts + 1 } }
      server (RegistrationServerSdkSource.accept setup (ledgerCodec wire) checks route mlSource.verify representation created packet)
  | .inr (.build session application) => server (RegistrationServerSdkSource.build setup (ledgerCodec wire) checks
      (RegistrationNativeMldsa.owned mlSource credential) wire.encodeResponse session application)
  | .inr (.finish owner packet) => beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.finish setup mlSource wire owner packet)
  | .inr (.hmac key message) => pure (setup.hmac.eval key message)
  | .inr (.hash bytes) => world (PqxdhRecordLiftWorld.effects (.inr (.hash bytes)))
  | .inr (.serverSend keyId plaintext) => record setup wire route (.inl (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => record setup wire route (.inl (.inr raw))
  | .inr (.beaconSend owner plaintext) => record setup wire route (.inr (owner, .inl plaintext))
  | .inr (.beaconRaw owner raw) => record setup wire route (.inr (owner, .inr raw))

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK mlSource) :=
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (handler setup checks wire route representation created credential)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).run before

end BeaconcryptCore.Computational.RegistrationNativeIdentityMain
