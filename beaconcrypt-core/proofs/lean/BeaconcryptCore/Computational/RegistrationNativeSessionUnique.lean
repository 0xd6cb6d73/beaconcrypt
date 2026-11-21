-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSessionLedger
import BeaconcryptCore.Computational.RegistrationNativeAcceptHandleProjection

/-! Successful accept handles are unique in the literal original registration ledger of each actual Native run. The source append invariant and exact ledger erasure discharge this property internally for the unchanged public matching event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSessionUnique
open RegistrationNativeExperiment (State)
open RegistrationNativeWire (Wire)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Every successful handle in the original public ledger names one literal raw accept candidate. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation
      created source credential bounds mode work before)) :
    ∀ raw other handle,
      PqxdhDeploymentServerAuthEvent.Reg.accept raw (some handle) ∈
        PqxdhDeploymentServerAuthEvent.regsOf result.2.1.ledger.transcript →
      PqxdhDeploymentServerAuthEvent.Reg.accept other (some handle) ∈
        PqxdhDeploymentServerAuthEvent.regsOf result.2.1.ledger.transcript →
      raw = other := by
  have complete := RegistrationNativeSessionLedger.run setup checks wire route representation created credential
    bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire
    created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
    mode work before result supported
  intro raw other handle left right
  rw [projected] at left right
  exact RegistrationNativeAcceptHandleProjection.unique_raw result.2.1.transcript
    result.2.2.server.sessions.length complete raw other handle left right

end BeaconcryptCore.Computational.RegistrationNativeSessionUnique

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionUnique.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionUnique.run
