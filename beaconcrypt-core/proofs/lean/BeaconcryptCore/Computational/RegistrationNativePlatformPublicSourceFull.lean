-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProgram
/-! The literal canonical-wire full raw compiler preserves its original ledger, Native security observation and shared platform poststate under the actual source interpreter. No event-correspondence condition is an input. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativePlatformPublicSourceGood (Good)
open RegistrationNativePublicSourceState (roots restore project nativeView)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def run (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) (previous : Platform) :=
  (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential))
    (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds mode work (front, previous))).run before

/-- The actual full raw source execution retains its complete original ledger and final runtime Native/P observation in every mode. -/
theorem run_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) (previous : Platform)
    (good : Good setup created.seed scalar selectedOwner ((front, previous), before)) :
    (fun result => ((result.1.1.1, (result.1.1.2, project (roots setup created.seed scalar) scalar result.1.2.1 result.2)), result.1.2.2)) <$>
      simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        (run setup checks wire route credential selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer (setup.dh.publicKey scalar) created.server.server.metadata.sender bounds mode work front before previous) =
      (fun result => ((result.1.1.1, (result.1.1.2, nativeView result.1.2)), result.2)) <$>
        (RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar bounds mode work
          (restore (roots setup created.seed scalar) scalar front before)).run previous := by
  have whole := RegistrationNativePlatformPublicSourceProgram.program_source setup checks wire route representation correct created credential
    selectedOwner selectedAccept scalar view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto (canonicalWire wire) created.server.server.metadata.sender bounds mode work)
    ((front, previous), before) good
  have mapped := congrArg (fun action => (fun result => ((result.1.1, (result.1.2, result.2.1)), result.2.2)) <$> action) whole
  simpa only [RegistrationNativePlatformPublicSourceProgram.view, RegistrationNativePlatformPublicSourceProgram.restoreState,
    RegistrationNativePlatformPublicSourceProgram.native, RegistrationAgreementNestedState.flatten,
    RegistrationNativePlatformPublicSourceExecution.execute, RegistrationNativePublicSourceEffects.close,
    run, RegistrationNativePlatformPublicFrontend.run, RegistrationNativePlatformOrdinaryScalarEager.run,
    StateT.run, simulateQ_map, Functor.map_map, Prod.map_def, id_eq, Function.comp_def, project] using mapped

/-- Any original full-ledger decision transfers on the same actual P, without observing projected instrumentation. -/
theorem ledger_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) (previous : Platform)
    (good : Good setup created.seed scalar selectedOwner ((front, previous), before))
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    (fun result => (decision result.1.1, result.1.2.2)) <$>
      simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        (run setup checks wire route credential selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer (setup.dh.publicKey scalar) created.server.server.metadata.sender bounds mode work front before previous) =
      (fun result => (decision result.1.1, result.2)) <$>
        (RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar bounds mode work
          (restore (roots setup created.seed scalar) scalar front before)).run previous := by
  have actual := run_source setup checks wire route credential selectedOwner selectedAccept scalar view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer representation correct created bounds mode work front before previous good
  have mapped := congrArg (fun action => (fun result => (decision (result.1.1, result.1.2.1), result.2)) <$> action) actual
  simpa only [Functor.map_map, Function.comp_def] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull.run_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull.ledger_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull.ledger_source
