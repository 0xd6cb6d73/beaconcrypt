-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed
/-! Actual corrected source Init publication and its stateful writer run on the same persistent P as the native platform bundle. Scalar restoration uses the derived public-owner mask equation, and the trusted role restriction is proved from the literal source controller, including failed publication and writer paths. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceBundle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSourceOwnerCommit (Output restoreOutput observe view commit)
open RegistrationNativePublicSourceState (restore project nativeView owners)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def work (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (index : Nat) :
    RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) (RustM (Option (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
    (RegistrationNativePlatformPublicFrontend.writer writer) setup source selected (setup.dh.publicKey scalar) index

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The actual owner-mask equation and free writer compilation determine the complete current owner/environment/P tree. -/
theorem equation (setup : Setup base KemSK)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (index : Nat)
    (frontend : RegistrationNativePublicFrontend.State source) (previous : Platform)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) frontend.beacons) :
    restoreOutput scalar <$> (((work (n := n) setup source writer selected scalar index).run frontend.beacons).run frontend.environment).run previous =
      simulateQ (RegistrationNativePlatformSourceOwnerEmbedding.embed (n := n))
        ((simulateQ (RegistrationNativePlatformSourceOwnerLanguage.handler (n := n) writer)
          (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run (owners scalar frontend.beacons)).run frontend.environment)).run previous) := by
  have masked := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformPublicOwners.bundle_source (RegistrationNativePlatformPublicFrontend.trusted (n := n) (Platform := Platform))
      (RegistrationNativePlatformPublicFrontend.writer writer) setup source selected scalar index frontend.beacons frontend.environment canonical)
  have evaluated := congrArg (fun action : RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) (RustM (Option (alloc.vec.Vec U8))) => ((action.run (owners scalar frontend.beacons)).run frontend.environment).run previous)
    (RegistrationNativePlatformGenericBundle.program_evaluate
      (fun query => match query with
        | .inl query => RegistrationNativePlatformPublicFrontend.trusted query
        | .inr query => RegistrationNativePlatformPublicFrontend.writer writer query) setup source index)
  have embedded := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformSourceOwnerLanguage.embedding_program writer
      (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run (owners scalar frontend.beacons)).run frontend.environment))
  unfold restoreOutput
  simpa only [work, StateT.run_map, StateT.run, map_apply, RegistrationNativePlatformGenericBundle.evaluate,
    RegistrationNativePlatformSourceOwnerLanguage.embedding, Prod.map_def, id_eq] using masked.trans (evaluated.symm.trans embedded.symm)

/-- The complete actual public bundle source callback agrees with literal native platform publication and the same stateful writer. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots) (index : Nat)
    (before : RegistrationNativePlatformPublicSourceExecution.State n KemSK Platform source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) before.1.1.beacons) :
    (fun result => ((RegistrationNativePlatformPublicFrontend.bundleBytes result.1,
      project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (RegistrationNativePlatformPublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.beacon (work (n := n) setup source writer selected scalar index)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformExperiment.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer index).run
          (restore roots scalar before.1.1 before.2)).run before.1.2 := by
  let tree := (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run (owners scalar before.1.1.beacons)).run before.1.1.environment)
  have safe := RegistrationNativePlatformSourceOwnerAllowed.compiled_safe writer tree
    (RegistrationNativePlatformSourceOwnerAllowed.program_safe setup index (owners scalar before.1.1.beacons) before.1.1.environment) before.1.2
  have raw := RegistrationNativePlatformSourceOwnerBody.raw_source setup checks wire route representation created scalar credential roots
    (work (n := n) setup source writer selected scalar index) ((simulateQ (RegistrationNativePlatformSourceOwnerLanguage.handler (n := n) writer) tree).run before.1.2)
    before (equation setup writer selected scalar index before.1.1 before.1.2 canonical) safe
  have target := RegistrationNativePlatformSourceOwnerBody.native_returned setup checks representation created writer tree
    (restore roots scalar before.1.1 before.2) before.1.2
  have combined := raw.trans target
  have mapped := congrArg (fun action => (fun result => ((RegistrationNativePlatformPublicFrontend.bundleBytes result.1.1, result.1.2), result.2)) <$> action) combined
  simpa only [Functor.map_map, Function.comp_def, RegistrationNativePlatformSourceOwnerBody.returned,
    RegistrationNativePlatformExperiment.bundle, RegistrationNativePlatformPublicFrontend.bundleBytes,
    StateT.run, map_apply, bind_pure_comp, RegistrationNativePlatformSourceOwnerCommit.view,
    RegistrationNativePlatformSourceOwnerCommit.commit, tree, restore,
    RegistrationWorldAgreementCompiler.erase, RegistrationWorldAgreementCompiler.join,
    RegistrationServerMaterialSourceState.restore, RegistrationServerReferenceRestore.restore, Prod.map_def, id_eq] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceBundle.equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceBundle.equation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceBundle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceBundle.bundle_source
