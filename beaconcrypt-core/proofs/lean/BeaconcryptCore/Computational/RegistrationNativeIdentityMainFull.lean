-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram

/-! The whole ordinary joint-service native client retains the unchanged original raw-CBOR compiler, complete hidden-bit and fresh-message ledger, every native reply and the full privately realized native poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainFull
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (interpret project Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def observedProject (result : RegistrationNativeEvents.Observed Value (State n KemSK mlSource) × SourceState) :
    RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK mlSource) :=
  (result.1.1, (result.1.2.1, project (result.1.2.2, result.2)))

/-- The complete actual original native raw experiment is recovered from the ordinary joint client, retaining the entire original secrecy ledger. -/
theorem full_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK mlSource × SourceState) (owned : Owned setup.joint before) :
    observedProject <$>
      (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
        (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work before.1)).run before.2 =
      RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work (project before) := by
  have law := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution)
    (RegistrationNativeIdentityMainProgram.program_source setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before owned)
  simp only [interpret, RegistrationNativeIdentityMain.run, RegistrationNativeExperiment.run,
    RegistrationNativeFullCompiler.compile_run, StateT.run, simulateQ_map,
    RegistrationNativeIdentityMainOrdinary.map_apply, Functor.map_map, Prod.map, id_eq,
    observedProject] at law ⊢
  exact law

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainFull

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainFull.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainFull.full_source
