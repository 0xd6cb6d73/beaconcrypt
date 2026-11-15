-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager
import BeaconcryptCore.Computational.RegistrationNativeMainViewLift
/-! The actual source build comparison is expressed in the same complete Native/P observation as every other corrected typed callback. Only the named instrumentation projection is composed; source cost and operational execution remain the literal marginal proved separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildTyped
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (roots restore project nativeView)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem project_world (roots : RegistrationServerReferenceRestore.Roots) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : State n KemSK Platform source) :
    nativeView (restore roots scalar (RegistrationNativePlatformPublicBuildJoint.stateView before).1.1
      (RegistrationNativePlatformPublicBuildJoint.stateView before).2) =
      project roots scalar before.1.1 before.2 := by
  simp only [RegistrationNativePlatformPublicBuildJoint.stateView, RegistrationNativePlatformPublicBuildClosure.worldView,
    nativeView, project, restore, RegistrationServerMaterialSourceState.nativeView,
    RegistrationServerMaterialSourceState.restore, RegistrationServerReferenceRestore.restore,
    RegistrationServerRecordWorldSource.project, RegistrationWorldAgreementCompiler.join,
    RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

/-- The actual moved-token public build is the literal final-runtime callback under the common full Native/P observation. -/
theorem build [primitive : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK Platform source)
    (live : RegistrationNativePublicSourceState.Live before.1.1 before.2)
    (correct : RegistrationNativePublicSourceState.MemoCorrect setup created.seed scalar before.2.roots) :
    (fun result => ((result.1, project (roots setup created.seed scalar) scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source
          (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build handle application)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryScalarEager.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar (.inr (.build handle application))).run
          (restore (roots setup created.seed scalar) scalar before.1.1 before.2)).run before.1.2 := by
  have actual := RegistrationNativePlatformPublicBuildRuntime.build setup checks wire route representation created credential scalar view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer handle application before live correct
  have mapped := congrArg (fun action => (fun result => ((result.1, nativeView result.2.1), result.2.2)) <$> action) actual
  simp only [Functor.map_map, RegistrationNativePlatformPublicBuildNative.restored,
    Prod.map_def, id_eq, project_world, RegistrationNativeMainViewLift.view_idempotent] at mapped
  convert mapped using 1 <;> rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildTyped.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildTyped.build
