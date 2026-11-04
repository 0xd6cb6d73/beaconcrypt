-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull
/-! Source observation extends to the actual reached World under its explicitly named accounting view. CTX cache, attempted produced frames and raw counters have a data-valued view that is literally invariant under that accounting projection. This is private analysis of the root-valued intermediate, not an extra public World-read capability for the opaque client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
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

def world (before : RegistrationNativeExperiment.State n KemSK source) : PqxdhRecordLiftWorld.State n :=
  before.server.world.world.1

abbrev RecordView := CtxRomAuth.CtxRO.QueryCache ×
  List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) × PqxdhRecordLiftWorld.RawCounters

def recordView (before : PqxdhRecordLiftWorld.State n) : RecordView :=
  (before.primitive.2, before.produced, PqxdhRecordLiftWorld.rawCounters before)

omit primitive in
/-- Root/scalar restoration does not change the World observation; only the separately billed source accounting view is applied. -/
theorem project_world (privateRoots : RegistrationServerReferenceRestore.Roots)
    (scalar : PqxdhJointGapDh.ScalarBytes) (front : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    world (project privateRoots scalar front before) = RegistrationNativeWorldView.project before.world := rfl

omit primitive in
/-- The literal source view preserves every retained CTX query, attempted produced frame and raw attempt counter. -/
theorem record_view (before : PqxdhRecordLiftWorld.State n) :
    recordView (RegistrationNativeWorldView.project before) = recordView before := rfl

omit primitive in
private theorem native_world (before : RegistrationNativeExperiment.State n KemSK source) :
    world (nativeView before) = RegistrationNativeWorldView.project (world before) := rfl

/-- Every World-view decision has the actual complete source/runtime law on the same final P, including source writer failures and attempted produced frames. -/
theorem world_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) (previous : Platform)
    (good : Good setup created.seed scalar selectedOwner ((front, previous), before))
    (decision : Value × RegistrationNativeLedger.State → PqxdhRecordLiftWorld.State n → Bool) :
    (fun result => (decision result.1.1 (RegistrationNativeWorldView.project result.2.world), result.1.2.2)) <$>
      simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationNativePlatformPublicSourceFull.run setup checks wire route credential selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer (setup.dh.publicKey scalar) created.server.server.metadata.sender bounds mode work front before previous) =
      (fun result => (decision result.1.1 (RegistrationNativeWorldView.project (world result.1.2)), result.2)) <$>
        (RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar bounds mode work
          (restore (roots setup created.seed scalar) scalar front before)).run previous := by
  have actual := RegistrationNativePlatformPublicSourceFull.run_source setup checks wire route credential selectedOwner selectedAccept scalar
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer representation correct created bounds mode work front before previous good
  have mapped := congrArg (fun action => (fun result =>
    (decision (result.1.1, result.1.2.1) (world result.1.2.2), result.2)) <$> action) actual
  simpa only [Functor.map_map, project_world, native_world] using mapped

/-- CTX-cache, crypto-produced-stage and raw-attempt decisions transfer on their exact literal source fields, with no event-invariance premise. -/
theorem record_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) (previous : Platform)
    (good : Good setup created.seed scalar selectedOwner ((front, previous), before))
    (decision : Value × RegistrationNativeLedger.State → RecordView → Bool) :
    (fun result => (decision result.1.1 (recordView result.2.world), result.1.2.2)) <$>
      simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationNativePlatformPublicSourceFull.run setup checks wire route credential selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer (setup.dh.publicKey scalar) created.server.server.metadata.sender bounds mode work front before previous) =
      (fun result => (decision result.1.1 (recordView (world result.1.2)), result.2)) <$>
        (RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar bounds mode work
          (restore (roots setup created.seed scalar) scalar front before)).run previous := by
  simpa only [record_view] using
    world_source setup checks wire route credential selectedOwner selectedAccept scalar view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer representation correct created bounds mode work front before previous good
      (fun result reached => decision result (recordView reached))
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.project_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.project_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.record_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.record_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.world_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation.record_source
