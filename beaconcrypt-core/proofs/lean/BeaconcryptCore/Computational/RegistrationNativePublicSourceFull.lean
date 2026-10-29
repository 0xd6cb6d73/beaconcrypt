-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram

/-! The actual public reference frontend preserves the entire original raw and secrecy ledger when closed with the literal source roots. This result includes failure replies and the complete permitted native poststate; no event-correspondence premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceFull
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The actual compiled full native interface has the same original ledger and the same semantic native poststate as the complete source execution. -/
theorem run_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativePublicInterpreter.State n KemSK)
    (good : RegistrationNativePublicSourceProgram.Good setup created.seed scalar selectedOwner (frontend, before)) :
    (fun result => (result.1.1.1, (result.1.1.2, RegistrationNativePublicSourceState.project
      (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar result.1.2 result.2))) <$>
      simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationNativePublicInterpreter.run setup checks wire route source credential selectedOwner selectedAccept
          (setup.dh.publicKey scalar) created.server.server.metadata.sender bounds mode work frontend before) =
      (fun result => (result.1, (result.2.1, RegistrationNativePublicSourceState.nativeView result.2.2))) <$>
        RegistrationNativeScalarEager.run setup checks wire route representation created source credential
          selectedOwner scalar bounds mode work
          (RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup created.seed scalar)
            scalar frontend before) := by
  have whole := RegistrationNativePublicSourceProgram.program_source setup checks wire route representation correct
    created scalar credential selectedOwner selectedAccept
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
    (frontend, before) good
  have mapped := congrArg (fun computation => (fun result => (result.1.1, (result.1.2, result.2))) <$> computation) whole
  rw [RegistrationNativeScalarEager.run, RegistrationNativeFullCompiler.compile_run]
  simp only [Functor.map_map] at mapped ⊢
  simpa only [RegistrationNativePublicSourceExecution.execute, RegistrationNativePublicSourceEffects.close,
    StateT.run, RegistrationNativePublicInterpreter.run, RegistrationNativePublicFrontend.run,
    simulateQ_map, Functor.map_map, Function.comp_def, Prod.map_def, id_eq] using mapped

/-- Any decision of the literal original full ledger transfers without inspecting the erased analysis counters or selected private scalars. -/
theorem ledger_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativePublicInterpreter.State n KemSK)
    (good : RegistrationNativePublicSourceProgram.Good setup created.seed scalar selectedOwner (frontend, before))
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    (fun result => decision result.1.1) <$>
      simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationNativePublicInterpreter.run setup checks wire route source credential selectedOwner selectedAccept
          (setup.dh.publicKey scalar) created.server.server.metadata.sender bounds mode work frontend before) =
      (fun result => decision (result.1, result.2.1)) <$>
        RegistrationNativeScalarEager.run setup checks wire route representation created source credential
          selectedOwner scalar bounds mode work
          (RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup created.seed scalar)
            scalar frontend before) := by
  have exactRun := run_source setup checks wire route representation correct created scalar credential selectedOwner selectedAccept
    bounds mode work frontend before good
  have mapped := congrArg (fun computation => (fun result => decision (result.1, result.2.1)) <$> computation) exactRun
  simpa only [Functor.map_map, Function.comp_def] using mapped

end BeaconcryptCore.Computational.RegistrationNativePublicSourceFull

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceFull.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceFull.run_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceFull.ledger_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceFull.ledger_source
