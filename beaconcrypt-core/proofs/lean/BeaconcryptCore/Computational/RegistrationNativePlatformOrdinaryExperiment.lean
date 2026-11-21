-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLower
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
/-! One corrected runtime profile retains the checked stateful registration callbacks and uses the actual dynamic source ordinary frame writer on all four established-record routes. The common platform state is shared across registration and ongoing traffic. The canonical frame writer is only the mathematical baseline codec; public reservation remains a separate runtime effect before the original ledger continuation. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeExperiment (State Initial Public)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhRecordLiftInterface (RecordQuery WorldSpec)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι}

abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Platform : Type) :=
  StateT (State n KemSK source) (StateT Platform ProbComp)

def canonicalWire (wire : Wire) : Wire := { wire with frameWrite := CborRawCanonicalBuild.canonicalWriter }

private theorem ledger_canonical (wire : Wire) :
    ledgerCodec (canonicalWire wire) = CborRawCanonicalBuild.canonical (ledgerCodec wire) := rfl

def replaceWorld {source : RegistrationNativeMldsa.Source} (before : State n KemSK source)
    (after : PqxdhRecordLiftWorld.State n) : State n KemSK source :=
  { before with server := { before.server with world := { before.server.world with world := (after, before.server.world.world.2) } } }

def world {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value) : M n KemSK source Platform Value :=
  fun before => (fun result => (result.1, replaceWorld before result.2)) <$> work.run before.server.world.world.1

noncomputable def record (setup : Setup base KemSK) (wire : Wire)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : RecordQuery) (source : RegistrationNativeMldsa.Source) :
    M n KemSK source Platform ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) :=
  match query with
  | .inl query => world (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route (.inr (.inr (.inl query))))
  | .inr (owner, .inl plaintext) => fun before => match before.beacons[owner]? with
      | none => pure (none, before)
      | some selected => (world (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))).run before
  | .inr (owner, .inr raw) => fun before => match before.beacons[owner]? with
      | none => pure (.None, before)
      | some selected => (world (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))).run before

noncomputable def handler [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl TypedSpec (M n KemSK source Platform)
  | .inr (.serverSend keyId plaintext) => record setup wire reserveFrame route (.inl (.inl (plaintext, keyId))) source
  | .inr (.serverRaw raw) => record setup wire reserveFrame route (.inl (.inr raw)) source
  | .inr (.beaconSend owner plaintext) => record setup wire reserveFrame route (.inr (owner, .inl plaintext)) source
  | .inr (.beaconRaw owner raw) => record setup wire reserveFrame route (.inr (owner, .inr raw)) source
  | query => RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks (canonicalWire wire)
      route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer query

noncomputable def run [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    StateT Platform ProbComp ((Value × RegistrationNativeLedger.State) × State n KemSK source) :=
  (simulateQ (handler setup checks wire route representation created source credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (canonicalWire wire) created.server.server.metadata.sender bounds mode work)).run before

noncomputable def profile [primitives : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) : StateT Platform ProbComp Bool := do
  let initialized ← StateT.lift (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure false
  | some initial =>
      (fun result => event (result.1.1, (result.1.2, result.2))) <$>
        run setup checks wire route representation initial.created source initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) initial.state

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
