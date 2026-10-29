-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents

/-! The concrete native dispatcher, including actual Server allocator gates and actual Beacon orchestration, retains the original CE observation and broad APP eligibility. The exact-bundle target is not substituted for that event. These operational equalities and query bills instantiate the complete compiler on the actual typed handler; cryptographic role/material/KEM and generated-startup composition remain separate obligations. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeExperimentProjection
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeInterface (ModeSpec Respects Entry)
open RegistrationNativeExperiment (State)
open PqxdhDeploymentInterface (Mode Budget FreshBounds)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Only native API analysis additions are projected; the original full secrecy ledger and actual produced frames are retained. -/
def observe {mlSource : RegistrationNativeMldsa.Source}
    (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource)) :
    PqxdhDeploymentKemTransfer.Observed Value :=
  (result.1, result.2.1.ledger, result.2.2.server.world.world.1.produced)

/-- The native event uses the original broad verified-key designation on the original ledger, including changed accepted packets. -/
theorem app_event (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : U64) (budget : Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) {mlSource : RegistrationNativeMldsa.Source}
    (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource)) :
    RegistrationNativeEvents.ceAppEvent crypto wire serverKid budget claim result =
      PqxdhDeploymentHeadlineEvents.appEvent crypto (ledgerCodec wire) serverKid budget claim (observe result) := rfl

/-- The complete concrete native run equals its actual typed compiled source, jointly over every original and new ledger field and all native private state. -/
theorem compile_run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (before : State n KemSK mlSource) :
    RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential)
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).run before :=
  RegistrationNativeFullCompiler.compile_run setup.source.crypto wire created.server.server.metadata.sender bounds _ mode work before

/-- Every actual supported native outcome derives the original transcript by dropping only the extra ML pin at public creation. -/
theorem ledger_projection (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (before : State n KemSK mlSource)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before)) :
    result.2.1.ledger.transcript = result.2.1.transcript.map Entry.erase :=
  RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire created.server.server.metadata.sender bounds _ mode work before result supported

/-- The concrete native APP trial is exactly the original headline event on the original complete observation. -/
theorem app_observation (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (work : OracleComp (ModeSpec .P) Value) (before : State n KemSK mlSource) :
    RegistrationNativeExperiment.app setup checks wire route representation created mlSource credential bounds budget claim work before =
      PqxdhDeploymentHeadlineEvents.appEvent setup.source.crypto (ledgerCodec wire) created.server.server.metadata.sender budget claim <$>
        (observe <$> RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds .P work before) := by
  rw [Functor.map_map]
  rfl

/-- The exact complete compiler transfers broad native APP probability, with no source-event equality premise or conditioning on registration success. -/
theorem app_compiled (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (work : OracleComp (ModeSpec .P) Value) (before : State n KemSK mlSource) :
    𝒟[RegistrationNativeExperiment.app setup checks wire route representation created mlSource credential bounds budget claim work before] {true} =
      𝒟[(fun result => PqxdhDeploymentHeadlineEvents.appEvent setup.source.crypto (ledgerCodec wire)
          created.server.server.metadata.sender budget claim (observe (result.1.1, (result.1.2, result.2)))) <$>
        (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential)
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds .P work)).run before] {true} := by
  rw [app_observation, compile_run, Functor.map_map, Functor.map_map]

/-- The actual native compiler retains all original twelve command bills, including the unchanged hidden-bit and fresh-byte allowances. -/
theorem compile_bound (setup : Setup base KemSK) (wire : Wire) (created : PqxdhLiveServerConstruction.Created Unit)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (budget : Budget)
    (bounded : Respects budget work) (kind : Fin 12) :
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = kind)
      (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds kind full * budget.cap full) :=
  RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire created.server.server.metadata.sender bounds mode work budget bounded kind

end BeaconcryptCore.Computational.RegistrationNativeExperimentProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.app_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.app_event
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.compile_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.compile_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.ledger_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.ledger_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.app_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.app_observation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.app_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.app_compiled
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentProjection.compile_bound
