-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence
import BeaconcryptCore.Computational.RegistrationNativeServerPinCached

/-! Actual initialized executions in every original raw observation mode retain both the complete configured pin fields and each owner's source prekey/scalar relation. The unchanged complete compiler supplies the literal typed execution; original test-bit and fresh-message sampling are preserved. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeServerPinCached (Configured)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (cached : Configured before.server.pin ⟨created.server.server.identity, created.server.server.metadata.sender⟩ credential.publicKey)
    (prekeys : RegistrationNativePrekeyCoherence.Holds setup before.beacons)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Configured result.2.2.server.pin ⟨created.server.server.identity, created.server.server.metadata.sender⟩ credential.publicKey ∧
      RegistrationNativePrekeyCoherence.Holds setup result.2.2.beacons := by
  rw [RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact ⟨RegistrationNativeServerPinCached.program_fields setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
      before cached inner possible,
    RegistrationNativePrekeyCoherence.program setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
      before prekeys inner possible⟩

/-- Both source operand receipts are derived for every initialized original raw run, without an invariant premise. -/
theorem initialized (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state)) :
    Configured result.2.2.server.pin ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ initial.credential.publicKey ∧
      RegistrationNativePrekeyCoherence.Holds setup result.2.2.beacons :=
  run setup checks wire route representation initial.created initial.credential bounds mode work initial.state
    (RegistrationNativeServerPinCached.start_fields setup ensureInit identityIndex serverKeyId initial started)
    (RegistrationNativePrekeyCoherence.start setup ensureInit identityIndex serverKeyId initial started) result supported

theorem fields (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state)) :
    result.2.2.server.pin.binding = ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ ∧
      result.2.2.server.pin.public_key = initial.credential.publicKey := by
  rw [RegistrationNativeServerPinTrace.run_pin setup checks wire route representation initial.created initial.credential bounds mode work initial.state result supported]
  exact RegistrationNativeServerPinStartup.start_pin setup source ensureInit identityIndex serverKeyId initial started

/-- Repeated selection returns the exact configured pin at an actual execution cut, with no state change or hash query. -/
theorem pin_selection (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state)) :
    (RegistrationNativeServerPinRecompute.native
      ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ initial.credential.publicKey).run
        result.2.2.server.world.world.1 =
      pure (.ok (.Some result.2.2.server.pin), result.2.2.server.world.world.1) := by
  obtain ⟨binding, key⟩ := fields setup checks wire route representation ensureInit identityIndex serverKeyId initial started bounds mode work result supported
  simpa only [binding, key] using RegistrationNativeServerPinRecompute.native_exact result.2.2.server.pin result.2.2.server.world.world.1

theorem owner (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state))
    (index : Nat) (selected : RegistrationNativeBeaconFrontend.Owner source) (found : result.2.2.beacons[index]? = some selected) :
    selected.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey selected.prekeyScalar) :=
  (initialized setup checks wire route representation ensureInit identityIndex serverKeyId initial started bounds mode work result supported).2
    selected (List.mem_of_getElem? found)

end BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.pin_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.pin_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun.owner
